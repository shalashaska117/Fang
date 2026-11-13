// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! recipe/mixed/generate-rectify.py: checked rectification and NNF goals for each declaration,
//! and `nnf`, the NNF renderer every later emitter uses.

use super::emit::{formula, term, vec};
use super::witness::{Formula, Witness};
use super::{Modules, Outcome, join, rejected};

/// `statistics(values)`.
fn statistics(values: &[u64]) -> String {
    format!(
        "⟨{}⟩",
        join(values.iter().map(|value| format!("{value}#usize")), ", ")
    )
}

/// `retained_bindings(value)`: the inactive stack the rectifier leaves, and the binder count.
fn retained_bindings(value: &Formula) -> Outcome<(Vec<(u64, u64)>, u64)> {
    struct Frames {
        entries: Vec<(u64, u64)>,
        active: usize,
        fresh: u64,
    }
    fn visit(node: &Formula, frames: &mut Frames) -> Outcome<()> {
        match node {
            Formula::All(binder, body) | Formula::Ex(binder, body) => {
                let binding = (*binder, frames.fresh);
                frames.fresh += 1;
                if frames.active < frames.entries.len() {
                    frames.entries[frames.active] = binding;
                } else {
                    frames.entries.push(binding);
                }
                frames.active += 1;
                visit(body, frames)?;
                frames.active -= 1;
            }
            Formula::Not(body) => visit(body, frames)?,
            Formula::Conj(left, right)
            | Formula::Disj(left, right)
            | Formula::Implies(left, right) => {
                visit(left, frames)?;
                visit(right, frames)?;
            }
            Formula::Atom(..) | Formula::Truth | Formula::Falsity => {}
            Formula::Literal(_) => return Err(rejected("Unsupported rectification witness shape")),
        }
        Ok(())
    }
    let mut frames = Frames {
        entries: Vec::new(),
        active: 0,
        fresh: 0,
    };
    visit(value, &mut frames)?;
    Ok((frames.entries, frames.fresh))
}

/// `nnf(g, value)`.
pub(crate) fn nnf(value: &Formula) -> Outcome<String> {
    Ok(match value {
        Formula::Truth => "(.True)".to_owned(),
        Formula::Falsity => "(.False)".to_owned(),
        Formula::Conj(left, right) => format!("(.And {} {})", nnf(left)?, nnf(right)?),
        Formula::Disj(left, right) => format!("(.Or {} {})", nnf(left)?, nnf(right)?),
        Formula::Literal(literal) => {
            let arguments: Vec<String> = literal
                .arguments
                .iter()
                .map(|argument| term(argument, false))
                .collect();
            format!(
                "(.Literal ⟨{}, {}#u32, {}⟩)",
                literal.positive,
                literal.predicate,
                vec(&arguments)
            )
        }
        Formula::All(binder, body) => format!("(.Forall {binder}#u32 {})", nnf(body)?),
        Formula::Ex(binder, body) => format!("(.Exists {binder}#u32 {})", nnf(body)?),
        _ => return Err(rejected("Unsupported NNF constructor")),
    })
}

const COMMON: &str = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Observed outputs are untrusted witnesses; Lean checks actual generated calls. -/\n";

/// `emit(g, witness, namespace)`: Rectify{i} and Normalize{i} for each declaration.
pub(crate) fn emit(witness: &Witness, namespace: &str) -> Outcome<Modules> {
    let intro = format!(
        "open Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nopen fang_skolem_core.fang_quantified_fof_core\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n"
    );
    let mut modules = Modules::new();
    for (index, (declaration, observed)) in witness
        .declarations
        .iter()
        .zip(&witness.standalone)
        .enumerate()
    {
        let rectified = format!("rectified{index}");
        let count = observed.binder_count;
        let (bindings, suggested_count) = retained_bindings(&declaration.formula)?;
        if suggested_count != count {
            return Err(rejected(
                "Observed binder count differs from suggested frame traversal",
            ));
        }
        let entries: Vec<String> = bindings
            .iter()
            .map(|(original, fresh)| format!("⟨{original}#u32, {fresh}#u32⟩"))
            .collect();
        let stack = format!("⟨{}, 0#usize⟩", vec(&entries));
        let mut code = format!(
            "{COMMON}import TransformPrimitives\nimport {namespace}Validate{index}\n{intro}"
        );
        code.push_str(&format!(
            "def {rectified} : Formula :=\n  {}\n",
            formula(&observed.rectified, false)?
        ));
        code.push_str(&format!(
            "def rectifiedStats{index} : Statistics := {}\n",
            statistics(&observed.rectified_stats)
        ));
        code.push_str(&format!(
            "theorem rectify{index}_body :\n  rectify_formula formula{index} ⟨alloc.vec.Vec.new _, 0#usize⟩ 0#u32 skolemLimits.core\n    ⟨{}⟩ =\n  .ok (.Ok {rectified}, {stack}, {count}#u32, ⟨rectifiedStats{index}⟩) := by\n",
            statistics(&observed.validated)
        ));
        code.push_str(&format!(
            "  simp only [formula{index}, {rectified}, rectifiedStats{index}]\n  generated_transform\n"
        ));
        code.push_str(&format!(
            "theorem rectify{index}_eq : rectify_closed formula{index} signature skolemLimits.core =\n    .ok (.Ok ⟨{rectified}, {count}#u32, rectifiedStats{index}⟩) :=\n  FangQuantifiedKernel.rectify_closed_of_parts _ _ _ _ _ _ _ _ validate{index}_eq rectify{index}_body\n"
        ));
        code.push_str(&format!(
            "#print axioms {namespace}.rectify{index}_body\n#print axioms {namespace}.rectify{index}_eq\nend {namespace}\n"
        ));
        modules.set(format!("{namespace}Rectify{index}"), code);
        let mut code = format!("{COMMON}import {namespace}Rectify{index}\n{intro}");
        code.push_str(&format!(
            "def normalized{index} : Nnf :=\n  {}\n",
            nnf(&observed.normalized)?
        ));
        code.push_str(&format!(
            "def normalizedStats{index} : Statistics := {}\n",
            statistics(&observed.normalized_stats)
        ));
        code.push_str(&format!(
            "theorem normalize{index}_body : normalize_formula {rectified} true skolemLimits.core ⟨rectifiedStats{index}⟩ =\n    .ok (.Ok normalized{index}, ⟨normalizedStats{index}⟩) := by\n"
        ));
        code.push_str(&format!(
            "  simp only [{rectified}, rectifiedStats{index}, normalized{index}, normalizedStats{index}]\n  generated_transform\n"
        ));
        code.push_str(&format!(
            "theorem normalize{index}_eq : rectify_normalize_closed formula{index} true signature skolemLimits.core =\n    .ok (.Ok ⟨normalized{index}, normalizedStats{index}⟩) := by\n  simp only [rectify_normalize_closed, rectify{index}_eq, bind_ok,\n    core.result.Result.Insts.CoreOpsTry.branch, normalize{index}_body, Aeneas.Std.uncurry]\n"
        ));
        code.push_str(&format!(
            "#print axioms {namespace}.normalize{index}_body\n#print axioms {namespace}.normalize{index}_eq\nend {namespace}\n"
        ));
        modules.set(format!("{namespace}Normalize{index}"), code);
    }
    Ok(modules)
}
