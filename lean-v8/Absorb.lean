/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact accounting for the actual public-call budget composition. -/
import Arithmetic

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

/-- Operation overflow preserves the incoming state. Once operations fit, the
    operation count is committed before the separate storage check. -/
def AbsorbPost (before : Work) (statistics : fang_quantified_fof_core.Statistics)
    (limits : Limits) (answer : core.result.Result Unit fang_skolem_core.Error × Work) : Prop :=
  if before.statistics.operations.val + statistics.operations.val ≤ limits.core.max_operations.val then
    ∃ operations, operations.val = before.statistics.operations.val + statistics.operations.val ∧
      AllocationAnswer { statistics := { before.statistics with operations := operations } }
        statistics.allocated_nodes limits answer
  else answer = (.Err (.Resource .Operations), before)

theorem absorb_spec (before : Work) (statistics : fang_quantified_fof_core.Statistics)
    (limits : Limits) :
    Work.absorb before statistics limits ⦃ AbsorbPost before statistics limits ⦄ := by
  unfold Work.absorb
  apply spec_bind (bounded_add_spec before.statistics.operations statistics.operations
    limits.core.max_operations .Operations)
  intro result checked
  unfold BoundedAnswer at checked
  split at checked
  next fits =>
    obtain ⟨operations, rfl, exactOperations⟩ := checked
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_mono (allocate_spec
      { statistics := { before.statistics with operations := operations } }
      statistics.allocated_nodes limits)
    intro answer allocated
    simp only [AbsorbPost, ite_eq_left fits]
    exact ⟨operations, exactOperations, allocated⟩
  next exceeds =>
    rw [checked]
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      AbsorbPost, exceeds]

theorem absorb_success {before after : Work} {statistics : fang_quantified_fof_core.Statistics}
    {limits : Limits} (success : Work.absorb before statistics limits = .ok (.Ok (), after)) :
    after.statistics.operations.val = before.statistics.operations.val + statistics.operations.val ∧
    after.statistics.allocated_nodes.val = before.statistics.allocated_nodes.val + statistics.allocated_nodes.val ∧
    after.statistics.operations.val ≤ limits.core.max_operations.val ∧
    after.statistics.allocated_nodes.val ≤ limits.core.max_stored_nodes.val := by
  have checked := absorb_spec before statistics limits
  rw [success] at checked
  simp only [spec_ok, AbsorbPost] at checked
  split at checked
  next fits =>
    obtain ⟨operations, exactOperations, allocated⟩ := checked
    unfold AllocationAnswer at allocated
    split at allocated
    next storageFits =>
      obtain ⟨nodes, equal, exactNodes⟩ := allocated
      cases equal
      exact ⟨exactOperations, exactNodes, by dsimp only; omega,
        by dsimp only at exactNodes storageFits ⊢; omega⟩
    next exceeds => cases allocated
  next exceeds => cases checked

end FangSkolemCore
