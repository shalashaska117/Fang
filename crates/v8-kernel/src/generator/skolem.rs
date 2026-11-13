// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! recipe/mixed/generate-skolem.py (`preparation`, the Preparation module) and
//! recipe/mixed/generate-transform.py (`public`, the Skolem module with the observed result).

use super::emit::vec;
use super::py;
use super::rectify::nnf;
use super::witness::Witness;
use super::{Modules, Outcome, join, require_namespace};

/// generate-skolem.py `emit(g, witness, namespace)`.
pub(crate) fn preparation(witness: &Witness, namespace: &str) -> Outcome<Modules> {
    require_namespace(namespace, "Invalid namespace")?;
    // Suggested private counters, not native observations. The emitted equations check the
    // actual calls including all remaining-budget calculations.
    let operations: u64 = witness
        .standalone
        .iter()
        .map(|value| value.validated[0] + 1)
        .sum();
    let stored: u64 = witness
        .standalone
        .iter()
        .map(|value| value.validated[3])
        .sum();
    let function_count = witness.functions.len() as u64;
    let predicate_count = witness.predicates.len() as u64;
    let common = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Suggested private counters are untrusted; Lean checks each actual call. -/\n";
    let mut code = format!(
        "{common}import TransformPrimitives\nimport {namespace}Encoded\nopen Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n"
    );
    code.push_str(&format!(
        "def validatedWork : fang_skolem_core.Work := ⟨⟨{operations}#usize, {stored}#usize⟩⟩\n"
    ));
    code.push_str("theorem validate_declarations_eq : fang_skolem_core.validate_declarations declarations signature skolemLimits\n  ⟨⟨0#usize, 0#usize⟩⟩ = .ok (.Ok (), validatedWork) := by\n");
    let mut names = vec![
        "declarations".to_owned(),
        "signature".to_owned(),
        "validatedWork".to_owned(),
    ];
    names.extend((0..witness.declarations.len()).map(|index| format!("formula{index}")));
    code.push_str(&format!(
        "  simp only [{}]\n  generated_transform\n",
        names.join(", ")
    ));
    code.push_str(&format!(
        "def functionsWork : fang_skolem_core.Work := ⟨⟨{}#usize, {}#usize⟩⟩\n",
        operations + function_count,
        stored + function_count
    ));
    code.push_str("theorem copy_functions_eq : fang_skolem_core.copy_arities (alloc.vec.Vec.deref signature.functions) skolemLimits validatedWork =\n    .ok (.Ok signature.functions, functionsWork) := by\n  simp only [signature, validatedWork, functionsWork]\n  generated_transform\n");
    code.push_str(&format!(
        "def preparedWork : fang_skolem_core.Work := ⟨⟨{}#usize, {}#usize⟩⟩\n",
        operations + function_count + predicate_count,
        stored + function_count + predicate_count
    ));
    code.push_str("theorem copy_predicates_eq : fang_skolem_core.copy_arities (alloc.vec.Vec.deref signature.predicates) skolemLimits functionsWork =\n    .ok (.Ok signature.predicates, preparedWork) := by\n  simp only [signature, functionsWork, preparedWork]\n  generated_transform\n");
    for name in [
        "validate_declarations_eq",
        "copy_functions_eq",
        "copy_predicates_eq",
    ] {
        code.push_str(&format!("#print axioms {namespace}.{name}\n"));
    }
    code.push_str(&format!("end {namespace}\n"));
    let mut modules = Modules::new();
    modules.set(format!("{namespace}Preparation"), code);
    Ok(modules)
}

/// generate-transform.py `emit(g, render_nnf, witness, namespace)`: the Skolem module.
pub(crate) fn public(witness: &Witness, namespace: &str) -> Outcome<String> {
    require_namespace(namespace, "Invalid namespace")?;
    let observed = &witness.skolem;
    let mut code = "/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.\n   Complete observed output is an untrusted witness to the actual public call. -/\n".to_owned();
    code.push_str(&format!(
        "import {namespace}Preparation\nimport TransformPrimitives\nimport SkolemProblemKernel\nopen Aeneas Aeneas.Std\nopen FangOriginalKernelProbe\nnamespace {namespace}\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n"
    ));
    let mut formulas = Vec::new();
    for value in &observed.formulas {
        formulas.push(nnf(value)?);
    }
    code.push_str(&format!(
        "def skolemized : fang_skolem_core.Skolemized := {{\n  formulas := {}\n",
        vec(&formulas)
    ));
    let functions: Vec<String> = observed
        .functions
        .iter()
        .map(|value| format!("{value}#usize"))
        .collect();
    // The Skolem predicate table was only compared with ==, so each entry prints as Python's str.
    let predicates: Vec<String> = observed
        .predicates
        .iter()
        .map(|value| format!("{}#usize", py::text(value)))
        .collect();
    code.push_str(&format!(
        "  signature := ⟨{}, {}⟩\n",
        vec(&functions),
        vec(&predicates)
    ));
    let origins: Vec<String> = observed
        .introduced
        .iter()
        .map(|origin| {
            let universals: Vec<String> = origin
                .universals
                .iter()
                .map(|value| format!("{value}#u32"))
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
    code.push_str(&format!(
        "  introduced := {}\n  statistics := ⟨{}⟩ }}\n",
        vec(&origins),
        join(
            observed
                .statistics
                .iter()
                .map(|value| format!("{value}#usize")),
            ", "
        )
    ));
    code.push_str("theorem skolemize_eq : fang_skolem_core.skolemize_problem declarations signature skolemLimits =\n    .ok (.Ok skolemized) := by\n");
    code.push_str("  have declarationsFit : ¬ Slice.len declarations > skolemLimits.max_declarations := by\n    simp [declarations, skolemLimits]\n");
    code.push_str("  have functionsFit : ¬ alloc.vec.Vec.len signature.functions >\n      core.cmp.impls.OrdUsize.min skolemLimits.max_functions\n        (UScalar.cast .Usize core.num.U32.MAX) := by\n    rw [FangQuantifiedKernel.function_cap]\n    simp [signature, FangQuantifiedKernel.vector, alloc.vec.Vec.val]\n");
    code.push_str("  unfold fang_skolem_core.skolemize_problem\n  rw [ite_eq_right declarationsFit]\n  simp only [lift, bind_ok]\n  rw [ite_eq_right functionsFit]\n  simp only [fang_skolem_core.Statistics.Insts.CoreDefaultDefault.default, default_value, bind_ok]\n  erw [validate_declarations_eq]\n  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry]\n  erw [copy_functions_eq]\n  simp only [bind_ok, Aeneas.Std.uncurry]\n  erw [copy_predicates_eq]\n  simp only [bind_ok, Aeneas.Std.uncurry]\n");
    code.push_str(&format!(
        "  simp only [declarations, signature, preparedWork, skolemized, {}]\n  generated_transform\n",
        join((0..witness.declarations.len()).map(|index| format!("formula{index}")), ", ")
    ));
    code.push_str(&format!(
        "#print axioms {namespace}.skolemize_eq\nend {namespace}\n"
    ));
    Ok(code)
}
