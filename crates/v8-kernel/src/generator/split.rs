// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! recipe/mixed/generate-split-transform.py (`suggest`, `transform`) and
//! recipe/mixed/generate-split-declarations.py (`declarations`).
//!
//! The traversal is untrusted witness construction: it suggests the private transformer
//! states, and every step it suggests must compile in Lean. Its result must equal the
//! observed public Skolem result.

use super::emit::{term, vec};
use super::rectify::nnf;
use super::skolem::public;
use super::witness::{Formula, Literal, Origin, Term, Witness};
use super::{Modules, Outcome, join, rejected, require_namespace};

const OPERATIONS: i64 = 5_000_000;
const STORED: i64 = 1_000_000;

/// A transformer state: `functions`, `introduced`, `entries`, `active`, `declaration`, `work`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct State {
    functions: Vec<u64>,
    introduced: Vec<Origin>,
    entries: Vec<u64>,
    active: usize,
    declaration: u64,
    work: [i64; 2],
}

/// One suggested `Transformer.transform` call.
#[derive(Clone, Debug)]
pub(crate) struct Node {
    index: usize,
    input: Formula,
    before: State,
    ticked: [i64; 2],
    allocated: Option<[i64; 2]>,
    left: Option<usize>,
    right: Option<usize>,
    pushed: Option<State>,
    child: Option<usize>,
    replacement: Option<Term>,
    introduced: Option<State>,
    substituted: Option<Formula>,
    substituted_work: Option<[i64; 2]>,
    value: Option<Formula>,
    after: Option<State>,
}

/// One declaration of the loop.
#[derive(Clone, Debug)]
pub(crate) struct Step {
    index: usize,
    before: State,
    ticked: [i64; 2],
    root: usize,
    after: State,
}

/// `initial_state(witness)`.
fn initial_state(witness: &Witness) -> State {
    let tables = (witness.functions.len() + witness.predicates.len()) as i64;
    let operations: i64 = witness
        .standalone
        .iter()
        .map(|value| value.validated[0] as i64 + 1)
        .sum();
    let stored: i64 = witness
        .standalone
        .iter()
        .map(|value| value.validated[3] as i64)
        .sum();
    State {
        functions: witness
            .functions
            .iter()
            .map(|symbol| symbol.arity)
            .collect(),
        introduced: Vec::new(),
        entries: Vec::new(),
        active: 0,
        declaration: 0,
        work: [operations + tables, stored + tables],
    }
}

/// `cost(work, operations, stored)`.
fn cost(work: &mut [i64; 2], operations: i64, stored: i64) -> Outcome<()> {
    work[0] += operations;
    work[1] += stored;
    if work[0] > OPERATIONS || work[1] > STORED {
        return Err(rejected(
            "Suggested state exceeds the declared replay limits",
        ));
    }
    Ok(())
}

fn copy_term(value: &Term, work: &mut [i64; 2]) -> Outcome<Term> {
    cost(work, 1, 1)?;
    if let Term::Fun(_, arguments) = value {
        for child in arguments {
            copy_term(child, work)?;
        }
    }
    Ok(value.clone())
}

fn substitute_term(
    value: &Term,
    binder: u64,
    replacement: &Term,
    work: &mut [i64; 2],
) -> Outcome<Term> {
    cost(work, 1, 0)?;
    if *value == Term::Var(binder) {
        return copy_term(replacement, work);
    }
    cost(work, 0, 1)?;
    match value {
        Term::Var(_) => Ok(value.clone()),
        Term::Fun(symbol, arguments) => {
            let mut changed = Vec::new();
            for child in arguments {
                changed.push(substitute_term(child, binder, replacement, work)?);
            }
            Ok(Term::Fun(*symbol, changed))
        }
    }
}

fn substitute(
    value: &Formula,
    binder: u64,
    replacement: &Term,
    active: bool,
    work: &mut [i64; 2],
) -> Outcome<Formula> {
    cost(work, 1, 1)?;
    Ok(match value {
        Formula::Literal(literal) => {
            let mut changed = Vec::new();
            for argument in &literal.arguments {
                changed.push(if active {
                    substitute_term(argument, binder, replacement, work)?
                } else {
                    copy_term(argument, work)?
                });
            }
            Formula::Literal(Literal {
                positive: literal.positive,
                predicate: literal.predicate,
                arguments: changed,
            })
        }
        Formula::All(bound, body) => Formula::All(
            *bound,
            Box::new(substitute(
                body,
                binder,
                replacement,
                active && *bound != binder,
                work,
            )?),
        ),
        Formula::Ex(bound, body) => Formula::Ex(
            *bound,
            Box::new(substitute(
                body,
                binder,
                replacement,
                active && *bound != binder,
                work,
            )?),
        ),
        Formula::Truth | Formula::Falsity => value.clone(),
        Formula::Conj(left, right) => {
            let left = substitute(left, binder, replacement, active, work)?;
            Formula::Conj(
                Box::new(left),
                Box::new(substitute(right, binder, replacement, active, work)?),
            )
        }
        Formula::Disj(left, right) => {
            let left = substitute(left, binder, replacement, active, work)?;
            Formula::Disj(
                Box::new(left),
                Box::new(substitute(right, binder, replacement, active, work)?),
            )
        }
        _ => return Err(rejected("Unsupported Skolem substitution constructor")),
    })
}

/// `transform(formula, current)`: appends the node and its descendants, returns its index and value.
fn transform(
    value: &Formula,
    current: &mut State,
    nodes: &mut Vec<Node>,
) -> Outcome<(usize, Formula)> {
    if nodes.len() >= 128 {
        return Err(rejected("Private-state suggestion limit exceeded"));
    }
    let index = nodes.len();
    nodes.push(Node {
        index,
        input: value.clone(),
        before: current.clone(),
        ticked: [0, 0],
        allocated: None,
        left: None,
        right: None,
        pushed: None,
        child: None,
        replacement: None,
        introduced: None,
        substituted: None,
        substituted_work: None,
        value: None,
        after: None,
    });
    cost(&mut current.work, 1, 0)?;
    nodes[index].ticked = current.work;
    let result = match value {
        Formula::Literal(_) | Formula::Truth | Formula::Falsity => {
            cost(&mut current.work, 0, 1)?;
            if let Formula::Literal(literal) = value {
                for argument in &literal.arguments {
                    copy_term(argument, &mut current.work)?;
                }
            }
            value.clone()
        }
        Formula::Conj(left, right) | Formula::Disj(left, right) => {
            cost(&mut current.work, 0, 1)?;
            nodes[index].allocated = Some(current.work);
            let (left_index, left_value) = transform(left, current, nodes)?;
            let (right_index, right_value) = transform(right, current, nodes)?;
            nodes[index].left = Some(left_index);
            nodes[index].right = Some(right_index);
            if matches!(value, Formula::Conj(..)) {
                Formula::Conj(Box::new(left_value), Box::new(right_value))
            } else {
                Formula::Disj(Box::new(left_value), Box::new(right_value))
            }
        }
        Formula::All(binder, body) => {
            cost(&mut current.work, 0, 1)?;
            nodes[index].allocated = Some(current.work);
            cost(&mut current.work, 1, 0)?;
            let active = current.active;
            if active < current.entries.len() {
                current.entries[active] = *binder;
            } else {
                cost(&mut current.work, 0, 1)?;
                current.entries.push(*binder);
            }
            current.active += 1;
            nodes[index].pushed = Some(current.clone());
            let (child, child_value) = transform(body, current, nodes)?;
            nodes[index].child = Some(child);
            current.active -= 1;
            Formula::All(*binder, Box::new(child_value))
        }
        Formula::Ex(binder, body) => {
            cost(&mut current.work, 1, 3)?;
            let dependencies: Vec<u64> = current.entries[..current.active].to_vec();
            let count = dependencies.len() as i64;
            cost(&mut current.work, count, 2 * count)?;
            let function = current.functions.len() as u64;
            let replacement = Term::Fun(
                function,
                dependencies
                    .iter()
                    .map(|&binder| Term::Var(binder))
                    .collect(),
            );
            current.functions.push(current.active as u64);
            current.introduced.push(Origin {
                declaration: current.declaration,
                binder: *binder,
                function,
                universals: dependencies,
            });
            nodes[index].replacement = Some(replacement.clone());
            nodes[index].introduced = Some(current.clone());
            let substituted = substitute(body, *binder, &replacement, true, &mut current.work)?;
            nodes[index].substituted = Some(substituted.clone());
            nodes[index].substituted_work = Some(current.work);
            let (child, child_value) = transform(&substituted, current, nodes)?;
            nodes[index].child = Some(child);
            child_value
        }
        _ => return Err(rejected("Unsupported Skolem transform constructor")),
    };
    nodes[index].value = Some(result.clone());
    nodes[index].after = Some(current.clone());
    Ok((index, result))
}

/// `suggest(witness)`: the nodes and the declaration steps.
fn suggest(witness: &Witness) -> Outcome<(Vec<Node>, Vec<Step>)> {
    let mut nodes = Vec::new();
    let mut steps = Vec::new();
    let mut state = initial_state(witness);
    let mut values = Vec::new();
    for (index, observation) in witness.standalone.iter().enumerate() {
        let before = state.clone();
        cost(&mut state.work, 1, 0)?;
        let ticked = state.work;
        let stats = &observation.normalized_stats;
        cost(&mut state.work, stats[0] as i64, stats[3] as i64)?;
        let (root, value) = transform(&observation.normalized, &mut state, &mut nodes)?;
        values.push(value);
        cost(&mut state.work, 0, 1)?;
        state.declaration += 1;
        steps.push(Step {
            index,
            before,
            ticked,
            root,
            after: state.clone(),
        });
    }
    let observed = &witness.skolem;
    let statistics: Vec<i64> = observed
        .statistics
        .iter()
        .map(|&value| value as i64)
        .collect();
    if values != observed.formulas
        || state.functions != observed.functions
        || state.introduced != observed.introduced
        || state.work[..] != statistics[..]
    {
        return Err(rejected(
            "Suggested private states do not match the observed public result",
        ));
    }
    Ok((nodes, steps))
}

fn work(value: &[i64; 2]) -> String {
    format!("⟨⟨{}#usize, {}#usize⟩⟩", value[0], value[1])
}

fn universals(value: &State) -> String {
    let entries: Vec<String> = value
        .entries
        .iter()
        .map(|entry| format!("{entry}#u32"))
        .collect();
    format!("⟨{}, {}#usize⟩", vec(&entries), value.active)
}

fn state(value: &State) -> String {
    let origins: Vec<String> = value
        .introduced
        .iter()
        .map(|origin| {
            let universals: Vec<String> = origin
                .universals
                .iter()
                .map(|entry| format!("{entry}#u32"))
                .collect();
            format!(
                "⟨{}#usize, {}#u32, {}#u32, {}⟩",
                origin.declaration,
                origin.binder,
                origin.function,
                vec(&universals)
            )
        })
        .collect();
    let functions: Vec<String> = value
        .functions
        .iter()
        .map(|arity| format!("{arity}#usize"))
        .collect();
    format!(
        "⟨{}, {}, {}, {}#usize, {}⟩",
        vec(&functions),
        vec(&origins),
        universals(value),
        value.declaration,
        work(&value.work)
    )
}

/// generate-split-transform.py `emit(g, render_nnf, witness, namespace)`: TransformData and
/// Transform{n}.
pub(crate) fn transform_modules(witness: &Witness, namespace: &str) -> Outcome<Modules> {
    require_namespace(namespace, "Invalid namespace")?;
    let (nodes, _) = suggest(witness)?;
    let common = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Suggested private states are untrusted; Lean checks actual generated calls. -/\n";
    let intro = format!(
        "open Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n"
    );
    let data_name = format!("{namespace}TransformData");
    let mut data = format!(
        "{common}import {namespace}Preparation\nimport BooleanTransformComposition\n{intro}"
    );
    for node in &nodes {
        let n = node.index;
        let states = [
            ("before", Some(&node.before)),
            ("after", node.after.as_ref()),
            ("pushed", node.pushed.as_ref()),
            ("introduced", node.introduced.as_ref()),
        ];
        for (field, value) in states {
            if let Some(value) = value {
                data.push_str(&format!(
                    "def t{n}_{field} : fang_skolem_core.Transformer := {}\n",
                    state(value)
                ));
            }
        }
        let works = [
            ("ticked", Some(&node.ticked)),
            ("allocated", node.allocated.as_ref()),
            ("substitutedWork", node.substituted_work.as_ref()),
        ];
        for (field, value) in works {
            if let Some(value) = value {
                data.push_str(&format!(
                    "def t{n}_{field} : fang_skolem_core.Work := {}\n",
                    work(value)
                ));
            }
        }
        let formulas = [
            ("input", Some(&node.input)),
            ("value", node.value.as_ref()),
            ("substituted", node.substituted.as_ref()),
        ];
        for (field, value) in formulas {
            if let Some(value) = value {
                data.push_str(&format!(
                    "def t{n}_{field} : fang_skolem_core.fang_quantified_fof_core.Nnf := {}\n",
                    nnf(value)?
                ));
            }
        }
        if let Some(replacement) = &node.replacement {
            data.push_str(&format!(
                "def t{n}_replacement : fang_skolem_core.fang.syntax.Term := {}\n",
                term(replacement, false)
            ));
        }
    }
    data.push_str(&format!("end {namespace}\n"));
    let mut modules = Modules::new();
    modules.set(data_name.clone(), data);
    for node in nodes.iter().rev() {
        let n = node.index;
        let name = format!("{namespace}Transform{n}");
        let mut imports = vec![data_name.clone()];
        if let Some(child) = node.child {
            imports.push(format!("{namespace}Transform{child}"));
        }
        if let (Some(left), Some(right)) = (node.left, node.right) {
            imports.push(format!("{namespace}Transform{left}"));
            imports.push(format!("{namespace}Transform{right}"));
        }
        let mut code = common.to_owned();
        for import in &imports {
            code.push_str(&format!("import {import}\n"));
        }
        code.push_str(&intro);
        if let Formula::Ex(binder, body) = &node.input {
            code.push_str(&format!(
                "theorem t{n}_introduce : fang_skolem_core.Transformer.introduce\n  {{ t{n}_before with work := t{n}_ticked }} {binder}#u32 skolemLimits =\n  .ok (.Ok t{n}_replacement, t{n}_introduced) := by\n"
            ));
            code.push_str(&format!(
                "  simp only [t{n}_before, t{n}_ticked, t{n}_replacement, t{n}_introduced]\n  generated_transform\n"
            ));
            code.push_str(&format!(
                "theorem t{n}_substitute : fang_skolem_core.substitute_nnf\n  {} {binder}#u32 t{n}_replacement true skolemLimits t{n}_introduced.work =\n  .ok (.Ok t{n}_substituted, t{n}_substitutedWork) := by\n",
                nnf(body)?
            ));
            code.push_str(&format!(
                "  simp only [t{n}_replacement, t{n}_introduced, t{n}_substituted, t{n}_substitutedWork]\n  generated_transform\n"
            ));
        }
        code.push_str(&format!(
            "theorem t{n}_transform : fang_skolem_core.Transformer.transform t{n}_before t{n}_input skolemLimits =\n  .ok (.Ok t{n}_value, t{n}_after) := by\n"
        ));
        match &node.input {
            Formula::Literal(_) | Formula::Truth | Formula::Falsity => {
                code.push_str(&format!(
                    "  simp only [t{n}_before, t{n}_input, t{n}_value, t{n}_after]\n  generated_transform\n"
                ));
            }
            Formula::All(..) => {
                let c = node.child.unwrap_or_default();
                code.push_str(&format!(
                    "  exact FangKernelGenerator.transform_forall_of_parts\n    (before := t{n}_before) (ticked := t{n}_ticked) (allocated := t{n}_allocated)\n    (pushed := t{n}_pushed.universals) (pushedWork := t{n}_pushed.work)\n    (changed := t{c}_after) (popped := t{n}_after.universals)\n"
                ));
                let groups: [&[&str]; 3] = [
                    &["before", "ticked"],
                    &["ticked", "allocated"],
                    &["before", "allocated", "pushed"],
                ];
                for fields in groups {
                    let names = join(fields.iter().map(|field| format!("t{n}_{field}")), ", ");
                    code.push_str(&format!(
                        "    (by simp only [{names}]; reduce_transform_primitives)\n"
                    ));
                }
                code.push_str(&format!(
                    "    t{c}_transform\n    (by simp only [t{c}_after, t{n}_after]; reduce_transform_primitives)\n"
                ));
            }
            Formula::Ex(..) => {
                let c = node.child.unwrap_or_default();
                code.push_str(&format!(
                    "  exact FangKernelGenerator.transform_exists_of_parts\n    (before := t{n}_before) (ticked := t{n}_ticked)\n    (by simp only [t{n}_before, t{n}_ticked]; reduce_transform_primitives)\n    t{n}_introduce t{n}_substitute t{c}_transform\n"
                ));
            }
            Formula::Conj(..) | Formula::Disj(..) => {
                let rule = if matches!(node.input, Formula::Conj(..)) {
                    "and"
                } else {
                    "or"
                };
                code.push_str(&format!(
                    "  exact FangKernelGenerator.transform_{rule}_of_parts\n    (before := t{n}_before) (ticked := t{n}_ticked) (allocated := t{n}_allocated)\n"
                ));
                let groups: [&[&str]; 2] = [&["before", "ticked"], &["ticked", "allocated"]];
                for fields in groups {
                    let names = join(fields.iter().map(|field| format!("t{n}_{field}")), ", ");
                    code.push_str(&format!(
                        "    (by simp only [{names}]; reduce_transform_primitives)\n"
                    ));
                }
                code.push_str(&format!(
                    "    t{}_transform t{}_transform\n",
                    node.left.unwrap_or_default(),
                    node.right.unwrap_or_default()
                ));
            }
            _ => {}
        }
        let fields: &[&str] = if matches!(node.input, Formula::Ex(..)) {
            &["introduce", "substitute", "transform"]
        } else {
            &["transform"]
        };
        for field in fields {
            code.push_str(&format!("#print axioms {namespace}.t{n}_{field}\n"));
        }
        code.push_str(&format!("end {namespace}\n"));
        modules.set(name, code);
    }
    Ok(modules)
}

/// generate-split-declarations.py `emit(g, render_nnf, split, public, witness, namespace)`.
pub(crate) fn declarations(witness: &Witness, namespace: &str) -> Outcome<Modules> {
    let (_, steps) = suggest(witness)?;
    let common = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Suggested private states are checked through the actual declaration loop. -/\n";
    let intro = format!(
        "open Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n"
    );
    let mut data = format!("{common}import {namespace}TransformData\nimport SkolemLoopKernel\n");
    for index in 0..steps.len() {
        data.push_str(&format!("import {namespace}Normalize{index}\n"));
    }
    data.push_str(&intro);
    for step in &steps {
        let i = step.index;
        data.push_str(&format!(
            "def loop{i}_before : fang_skolem_core.Transformer := {}\n",
            state(&step.before)
        ));
        data.push_str(&format!(
            "def loop{i}_ticked : fang_skolem_core.Work := {}\n",
            work(&step.ticked)
        ));
        data.push_str(&format!(
            "def loop{i}_remaining : fang_skolem_core.fang_quantified_fof_core.Limits :=\n  {{ skolemLimits.core with max_operations := {}#usize, max_stored_nodes := {}#usize }}\n",
            OPERATIONS - step.ticked[0],
            STORED - step.ticked[1]
        ));
    }
    let count = steps.len();
    let final_state = match steps.last() {
        Some(step) => step.after.clone(),
        None => initial_state(witness),
    };
    data.push_str(&format!(
        "def loop{count}_before : fang_skolem_core.Transformer := {}\n",
        state(&final_state)
    ));
    for i in 0..=count {
        data.push_str(&format!(
            "def loop{i}_outputs : alloc.vec.Vec fang_skolem_core.fang_quantified_fof_core.Nnf := "
        ));
        let outputs: Vec<String> = steps[..i]
            .iter()
            .map(|step| format!("t{}_value", step.root))
            .collect();
        data.push_str(&vec(&outputs));
        data.push('\n');
    }
    data.push_str(&format!("end {namespace}\n"));
    let mut modules = Modules::new();
    modules.set(format!("{namespace}LoopData"), data);
    if steps.is_empty() {
        let mut code = format!("{common}import {namespace}LoopData\n{intro}");
        code.push_str("theorem loop0_eq : fang_skolem_core.transform_declarations_loop declarations signature skolemLimits\n  loop0_before loop0_outputs = .ok (.Ok loop0_outputs, loop0_before) := by\n");
        code.push_str("  exact FangQuantifiedKernel.declarations_finished declarations signature skolemLimits\n    loop0_before loop0_outputs (by simp [loop0_before, declarations])\n");
        code.push_str(&format!(
            "#print axioms {namespace}.loop0_eq\nend {namespace}\n"
        ));
        modules.set(format!("{namespace}DeclarationLoop0"), code);
    }
    for step in &steps {
        let i = step.index;
        let mut code = format!("{common}import {namespace}LoopData\n{intro}");
        code.push_str(&format!(
            "theorem normalize_remaining{i} : fang_skolem_core.fang_quantified_fof_core.rectify_normalize_closed\n  formula{i} true signature loop{i}_remaining = .ok (.Ok ⟨normalized{i}, normalizedStats{i}⟩) := by\n"
        ));
        code.push_str(&format!(
            "  simp only [formula{i}, signature, loop{i}_remaining, normalized{i}, normalizedStats{i}]\n  generated_transform\n"
        ));
        code.push_str(&format!(
            "#print axioms {namespace}.normalize_remaining{i}\nend {namespace}\n"
        ));
        modules.set(format!("{namespace}NormalizeRemaining{i}"), code);
    }
    for step in steps.iter().rev() {
        let (i, root) = (step.index, step.root);
        let next = i + 1;
        let mut code = format!(
            "{common}import {namespace}NormalizeRemaining{i}\nimport {namespace}Transform{root}\n"
        );
        if next < count {
            code.push_str(&format!("import {namespace}DeclarationLoop{next}\n"));
        }
        code.push_str(&intro);
        code.push_str(&format!(
            "theorem loop{i}_eq : fang_skolem_core.transform_declarations_loop declarations signature skolemLimits\n  loop{i}_before loop{i}_outputs = .ok (.Ok loop{count}_outputs, loop{count}_before) := by\n"
        ));
        code.push_str(&format!(
            "  apply FangQuantifiedKernel.declaration_step declarations signature skolemLimits loop{i}_before\n    loop{i}_outputs ⟨formula{i}, true⟩ loop{i}_ticked loop{i}_remaining\n    ⟨normalized{i}, normalizedStats{i}⟩ t{root}_before.work t{root}_value t{root}_after\n    loop{next}_before.work loop{next}_outputs {next}#usize loop{count}_outputs loop{count}_before\n"
        ));
        code.push_str(&format!("  · simp [loop{i}_before, declarations]\n"));
        code.push_str(&format!(
            "  · simp only [loop{i}_before, loop{i}_ticked]\n    reduce_transform_primitives\n"
        ));
        code.push_str(&format!(
            "  · simp (disch := kernel_scalar) [loop{i}_before, declarations, Slice.index_usize]\n"
        ));
        code.push_str(&format!(
            "  · simp only [loop{i}_ticked, loop{i}_remaining]\n    reduce_transform_primitives\n"
        ));
        code.push_str(&format!("  · exact normalize_remaining{i}\n"));
        code.push_str(&format!(
            "  · simp only [loop{i}_ticked, normalizedStats{i}, t{root}_before]\n    reduce_transform_primitives\n"
        ));
        code.push_str(&format!("  · exact t{root}_transform\n"));
        code.push_str(&format!(
            "  · simp only [t{root}_after, loop{next}_before]\n    reduce_transform_primitives\n"
        ));
        code.push_str(&format!(
            "  · simp only [loop{i}_outputs, loop{next}_outputs]\n    reduce_transform_primitives\n"
        ));
        code.push_str(&format!(
            "  · simp only [loop{i}_before]\n    reduce_transform_primitives\n"
        ));
        code.push_str("  · rfl\n");
        if next < count {
            code.push_str(&format!("  · exact loop{next}_eq\n"));
        } else {
            code.push_str(&format!(
                "  · exact FangQuantifiedKernel.declarations_finished declarations signature skolemLimits\n      loop{count}_before loop{count}_outputs (by simp [loop{count}_before, declarations])\n"
            ));
        }
        code.push_str(&format!(
            "#print axioms {namespace}.loop{i}_eq\nend {namespace}\n"
        ));
        modules.set(format!("{namespace}DeclarationLoop{i}"), code);
    }
    let result = public(witness, namespace)?;
    let result = result.replace(
        &format!("import {namespace}Preparation\n"),
        &format!("import {namespace}DeclarationLoop0\n"),
    );
    let marker = "  simp only [declarations, signature, preparedWork, skolemized,";
    let Some(begin) = result.find(marker) else {
        return Err(rejected("substring not found"));
    };
    if !result[begin..].contains("#print axioms") {
        return Err(rejected("substring not found"));
    }
    let mut skolem = result[..begin].to_owned();
    skolem.push_str("  unfold fang_skolem_core.transform_declarations\n  erw [loop0_eq]\n  simp only [bind_ok, Aeneas.Std.uncurry]\n");
    skolem.push_str(&format!(
        "  rfl\n#print axioms {namespace}.skolemize_eq\nend {namespace}\n"
    ));
    modules.set(format!("{namespace}Skolem"), skolem);
    Ok(modules)
}
