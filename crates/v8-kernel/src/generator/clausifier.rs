// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! recipe/mixed/generate-clausifier.py: the clausifier equations, preserving the observed
//! clause and literal order.

use super::emit::{term, vec};
use super::rectify::nnf;
use super::removal::without_universals;
use super::witness::{Literal, Witness};
use super::{Modules, Outcome, join, require_namespace};

/// `literal(g, value)`.
fn literal(value: &Literal) -> String {
    let arguments: Vec<String> = value
        .arguments
        .iter()
        .map(|argument| term(argument, false))
        .collect();
    format!(
        "⟨{}, {}#u32, {}⟩",
        value.positive,
        value.predicate,
        vec(&arguments)
    )
}

/// `emit(g, render_nnf, removal, witness, namespace)`: Clausify{i} for each block.
pub(crate) fn emit(witness: &Witness, namespace: &str) -> Outcome<Modules> {
    require_namespace(namespace, "Invalid namespace")?;
    let mut modules = Modules::new();
    for (index, (formula, block)) in witness
        .skolem
        .formulas
        .iter()
        .zip(&witness.blocks)
        .enumerate()
    {
        let erased = without_universals(formula)?;
        let clauses: Vec<String> = block
            .clauses
            .iter()
            .map(|clause| vec(&clause.iter().map(literal).collect::<Vec<_>>()))
            .collect();
        let clauses = vec(&clauses);
        let mut code = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Observed clauses and counters are untrusted; Lean checks the actual call. -/\n".to_owned();
        code.push_str(&format!(
            "import BooleanClausifierSinglePass\nimport {namespace}Removal{index}\nopen Aeneas Aeneas.Std\nnamespace {namespace}\n"
        ));
        code.push_str("set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n");
        code.push_str(&format!(
            "def block{index} : fang_fof_core.Preprocessed :=\n  ⟨{clauses}, ⟨{}⟩⟩\n",
            join(
                block
                    .clausifier_stats
                    .iter()
                    .map(|value| format!("{value}#usize")),
                ", "
            )
        ));
        code.push_str(&format!(
            "theorem clausify{index}_eq : fang_fof_core.nnf_entry.clausify_nnf_from\n    (FangQuantifiedPipeline.removedNnf removed{index}.formula) FangQuantifiedKernel.Clausifier.limits\n    FangOriginalReplay.initialStatistics = .ok (.Ok block{index}) := by\n"
        ));
        code.push_str(&format!(
            "  change fang_fof_core.nnf_entry.clausify_nnf_from {}\n    FangQuantifiedKernel.Clausifier.limits FangOriginalReplay.initialStatistics = .ok (.Ok block{index})\n",
            nnf(&erased)?
        ));
        code.push_str(&format!(
            "  simp only [block{index}]\n  generated_boolean_clausifier_single\n"
        ));
        code.push_str(&format!(
            "#print axioms {namespace}.clausify{index}_eq\nend {namespace}\n"
        ));
        modules.set(format!("{namespace}Clausify{index}"), code);
    }
    Ok(modules)
}
