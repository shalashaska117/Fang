/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Proof-producing, bounded unfolding of closed calls to the captured model.
   No generated definition is replaced. Lean checks each resulting proof term. -/
import OriginalReplay
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Unfold

open Lean Meta Elab Tactic
namespace FangBooleanClausifierGenerator

private def allowed : List Name := [
  ``fang_fof_core.copy_term,
  ``fang_fof_core.copy_term_loop,
  ``fang_fof_core.copy_arguments,
  ``fang_fof_core.copy_arguments_loop,
  ``fang_fof_core.copy_literal,
  ``fang_fof_core.append_literals_loop,
  ``fang_fof_core.append_literals,
  ``fang_fof_core.append_clauses_loop,
  ``fang_fof_core.append_clauses,
  ``fang_fof_core.append_cnf,
  ``fang_fof_core.product_row_loop,
  ``fang_fof_core.product_row,
  ``fang_fof_core.product_cnf_loop,
  ``fang_fof_core.product_cnf,
  ``fang_fof_core.clausify_nnf,
  ``fang_fof_core.nnf_entry.clausify_nnf_from]

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

elab "closed_boolean_clausifier_step" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let context ← Simp.mkContext (congrTheorems := (← getSimpCongrTheorems))
      (config := { Simp.neutralConfig with letToHave := true })
    let (result, _) ← Simp.main target context (methods := { pre := closedUnfold })
    if result.expr == target then
      throwError "No supported closed generated call is ready\n{target}"
    replaceMainGoal [← applySimpResultToTarget goal target result]

end FangBooleanClausifierGenerator
