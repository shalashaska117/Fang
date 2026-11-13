/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Ordered signature copying for the actual generated public call. -/
import Absorb

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

def ArityCopyPost (arities : Slice Usize) (index : Usize) (before : Work)
    (answer : core.result.Result (alloc.vec.Vec Usize) fang_skolem_core.Error × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.statistics.operations.val ∧
  before.statistics.allocated_nodes.val ≤ answer.2.statistics.allocated_nodes.val ∧
  match answer.1 with
  | .Ok copied => copied.val = arities.val ∧
      answer.2.statistics.operations.val = before.statistics.operations.val + (arities.val.length - index.val) ∧
      answer.2.statistics.allocated_nodes.val = before.statistics.allocated_nodes.val + (arities.val.length - index.val)
  | .Err (.Resource kind) => kind = .Operations ∨ kind = .StoredNodes
  | .Err (.Core _) => False

theorem copy_arities_loop_spec (arities : Slice Usize) (limits : Limits) (work : Work)
    (copied : alloc.vec.Vec Usize) (index : Usize) (inside : index.val ≤ arities.val.length)
    (copiedPrefix : copied.val = arities.val.take index.val) :
    copy_arities_loop arities limits work copied index ⦃ ArityCopyPost arities index work ⦄ := by
  unfold copy_arities_loop
  dsimp only
  split
  next more =>
    have hi : index.val < arities.val.length := by scalar_tac
    have copiedLength : copied.val.length = index.val := by
      rw [copiedPrefix, List.length_take]
      omega
    apply spec_bind (tick_spec work limits)
    intro answer ticked
    unfold TickAnswer at ticked
    split at ticked
    next fits =>
      obtain ⟨operation, rfl, operation_eq⟩ := ticked
      simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (allocate_spec _ 1#usize limits)
      intro answer allocated
      unfold AllocationAnswer at allocated
      split at allocated
      next storageFits =>
        obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
        simp only [Aeneas.Std.uncurry, bind_ok]
        apply spec_bind (Slice.index_usize_spec arities index hi)
        intro value same
        subst value
        apply spec_bind (alloc.vec.Vec.push_spec copied arities.val[index.val] (by
          have := arities.property
          omega))
        intro nextCopied copied_eq
        apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        intro next next_eq
        have nextval : next.val = index.val + 1 := by simpa using next_eq
        have nextPrefix : nextCopied.val = arities.val.take next.val := by
          rw [copied_eq, copiedPrefix, nextval]
          exact (List.take_succ_eq_append_getElem hi).symm
        apply spec_mono (copy_arities_loop_spec arities limits _ nextCopied next
          (by scalar_tac) nextPrefix)
        rintro ⟨result, after⟩ ⟨hm, hs, post⟩
        dsimp only at hm hs post
        refine ⟨by dsimp only; omega, by dsimp only; scalar_tac, ?_⟩
        cases result with
        | Err error => cases error <;> exact post
        | Ok result =>
          obtain ⟨same, operations, storage⟩ := post
          exact ⟨same, by dsimp only; scalar_tac, by dsimp only; scalar_tac⟩
      next storageExceeded =>
        rw [allocated]
        have post : ArityCopyPost arities index work (.Err (.Resource .StoredNodes),
            { statistics := { work.statistics with operations := operation } }) := by
          exact ⟨by dsimp only; omega, Nat.le_refl _, Or.inr rfl⟩
        simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    next exceeded =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, ArityCopyPost]
  next done =>
    have last : index.val = arities.val.length := by scalar_tac
    simp [ArityCopyPost, copiedPrefix, last]
termination_by arities.val.length - index.val
decreasing_by scalar_tac

theorem copy_arities_spec (arities : Slice Usize) (limits : Limits) (work : Work) :
    copy_arities arities limits work ⦃ ArityCopyPost arities 0#usize work ⦄ := by
  unfold copy_arities
  exact copy_arities_loop_spec arities limits work _ _ (by simp) (by simp)

end FangSkolemCore
