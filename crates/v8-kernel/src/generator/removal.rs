// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! recipe/mixed/generate-removal.py: the binder-removal equations from the Skolem output.

use super::rectify::nnf;
use super::witness::{Formula, Witness};
use super::{Modules, Outcome, join, rejected, require_namespace};

/// `without_universals(g, value)`: the suggested erasure. The emitted equation checks the
/// unchanged remover on the complete input, including every universal node.
pub(crate) fn without_universals(value: &Formula) -> Outcome<Formula> {
    let mut value = value;
    while let Formula::All(_, body) = value {
        value = body;
    }
    match value {
        Formula::Literal(_) | Formula::Truth | Formula::Falsity => Ok(value.clone()),
        Formula::Conj(left, right) => {
            let left = without_universals(left)?;
            Ok(Formula::Conj(
                Box::new(left),
                Box::new(without_universals(right)?),
            ))
        }
        Formula::Disj(left, right) => {
            let left = without_universals(left)?;
            Ok(Formula::Disj(
                Box::new(left),
                Box::new(without_universals(right)?),
            ))
        }
        _ => Err(rejected("Unsupported removal witness constructor")),
    }
}

/// `emit(g, render_nnf, witness, namespace)`: Removal{i} for each Skolem output.
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
        let mut code = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Expected erasure and counters are untrusted; Lean checks the actual call. -/\n".to_owned();
        code.push_str(&format!(
            "import RemovalPrimitives\nimport {namespace}Encoded\nopen Aeneas Aeneas.Std\nnamespace {namespace}\n"
        ));
        code.push_str("set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n");
        let rendered = nnf(formula)?;
        code.push_str(&format!("def skolemOutput{index} : fang_skolem_core.fang_quantified_fof_core.Nnf :=\n  {rendered}\n"));
        code.push_str(&format!(
            "def removed{index} : fang_binder_removal_core.Removed :=\n  ⟨{}, ⟨{}⟩⟩\n",
            nnf(&erased)?,
            join(
                block
                    .removal_stats
                    .iter()
                    .map(|value| format!("{value}#usize")),
                ", "
            )
        ));
        code.push_str(&format!(
            "theorem remove{index}_eq : fang_binder_removal_core.remove_universals\n    (FangQuantifiedPipeline.skolemNnf skolemOutput{index}) FangKernelGenerator.removalLimits =\n    .ok (.Ok removed{index}) := by\n"
        ));
        code.push_str(&format!(
            "  change fang_binder_removal_core.remove_universals {rendered}\n    FangKernelGenerator.removalLimits = .ok (.Ok removed{index})\n  simp only [removed{index}]\n  generated_removal\n"
        ));
        code.push_str(&format!(
            "#print axioms {namespace}.remove{index}_eq\nend {namespace}\n"
        ));
        modules.set(format!("{namespace}Removal{index}"), code);
    }
    Ok(modules)
}
