/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Proof-producing, bounded unfolding of closed calls to the captured model.
   No generated definition is replaced. Lean checks each resulting proof term. -/
import CoreArithmeticKernel
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Unfold

open Lean Meta Elab Tactic
namespace FangSkolemGenerator

private def allowed : List Name := [
  ``fang_skolem_core.fang_quantified_fof_core.validate_formula,
  ``fang_skolem_core.fang_quantified_fof_core.validate_formula_loop,
  ``fang_skolem_core.fang_quantified_fof_core.validate_term,
  ``fang_skolem_core.fang_quantified_fof_core.validate_term_loop,
  ``fang_skolem_core.fang_quantified_fof_core.bound_name,
  ``fang_skolem_core.fang_quantified_fof_core.bound_name_loop,
  ``fang_skolem_core.fang_quantified_fof_core.copy_term,
  ``fang_skolem_core.fang_quantified_fof_core.copy_term_loop,
  ``fang_skolem_core.fang_quantified_fof_core.copy_arguments,
  ``fang_skolem_core.fang_quantified_fof_core.copy_arguments_loop,
  ``fang_skolem_core.fang_quantified_fof_core.lookup_binding,
  ``fang_skolem_core.fang_quantified_fof_core.lookup_binding_loop,
  ``fang_skolem_core.fang_quantified_fof_core.rectify_formula,
  ``fang_skolem_core.fang_quantified_fof_core.normalize_formula,
  ``fang_skolem_core.fang_quantified_fof_core.validate,
  ``fang_skolem_core.fang_quantified_fof_core.validate_with_scope,
  ``fang_skolem_core.fang_quantified_fof_core.rectify_closed,
  ``fang_skolem_core.fang_quantified_fof_core.rectify_normalize_closed,
  ``fang_skolem_core.validate_declarations,
  ``fang_skolem_core.validate_declarations_loop,
  ``fang_skolem_core.copy_arities,
  ``fang_skolem_core.copy_arities_loop,
  ``fang_skolem_core.copy_dependencies,
  ``fang_skolem_core.copy_dependencies_loop,
  ``fang_skolem_core.copy_term,
  ``fang_skolem_core.copy_term_loop,
  ``fang_skolem_core.copy_literal,
  ``fang_skolem_core.copy_literal_loop,
  ``fang_skolem_core.substitute_term,
  ``fang_skolem_core.substitute_term_loop,
  ``fang_skolem_core.substitute_nnf,
  ``fang_skolem_core.substitute_nnf_loop,
  ``fang_skolem_core.Transformer.introduce,
  ``fang_skolem_core.Transformer.transform,
  ``fang_skolem_core.transform_declarations,
  ``fang_skolem_core.transform_declarations_loop,
  ``fang_skolem_core.skolemize_problem]

private def closedUnfold (e : Expr) : SimpM Simp.Step := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .continue
  let some declaration := e.getAppFn.constName? | return .continue
  if !allowed.contains declaration then return .continue
  let some equation ← getUnfoldEqnFor? declaration | do
    let reduced ← deltaExpand e (· == declaration)
    if reduced == e then return .continue
    return .done { expr := reduced }
  let some result ← withReducible <| Simp.tryTheorem? e {
      origin := .decl equation, proof := mkConst equation,
      rfl := (← isRflTheorem equation), backwardRfl := (← isBackwardRflTheorem equation) }
    | return .continue
  match ← reduceMatcher? result.expr with
  | .reduced reduced => return .done { result with expr := reduced }
  | _ => return .done result

elab "closed_skolem_step" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let context ← Simp.mkContext (congrTheorems := (← getSimpCongrTheorems))
      (config := { Simp.neutralConfig with letToHave := true })
    let (result, _) ← Simp.main target context (methods := { pre := closedUnfold })
    if result.expr == target then
      throwError "No supported closed generated call is ready\n{target}"
    replaceMainGoal [← applySimpResultToTarget goal target result]

end FangSkolemGenerator
