/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Proof-producing, bounded unfolding of closed calls to the captured model.
   No generated definition is replaced. Lean checks each resulting proof term. -/
import OriginalReplay
import Lean.Elab.Tactic
import Lean.Meta.Tactic.Unfold

open Lean Meta Elab Tactic
namespace FangRemovalGenerator

private def allowed : List Name := [
  ``fang_binder_removal_core.remove,
  ``fang_binder_removal_core.remove_universals]

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

elab "closed_removal_step" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let context ← Simp.mkContext (congrTheorems := (← getSimpCongrTheorems))
      (config := { Simp.neutralConfig with letToHave := true })
    let (result, _) ← Simp.main target context (methods := { pre := closedUnfold })
    if result.expr == target then
      throwError "No supported closed generated call is ready\n{target}"
    replaceMainGoal [← applySimpResultToTarget goal target result]

end FangRemovalGenerator
