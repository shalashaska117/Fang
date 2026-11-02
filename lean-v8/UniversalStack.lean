/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Direct active-prefix contracts for the actual generated universal stack. -/
import Introduce

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

def UniversalValid (stack : Universals) : Prop := stack.active.val ≤ stack.entries.val.length

def UniversalPushedEntries (stack : Universals) (id : U32) : List U32 :=
  if stack.active.val < stack.entries.val.length then stack.entries.val.set stack.active.val id
  else stack.entries.val ++ [id]

/-- Inactive storage is outside the caller's logical stack frame. -/
def UniversalFrame (before after : Universals) : Prop :=
  after.active.val = before.active.val ∧
  ∀ i, i < before.active.val → after.entries.val[i]? = before.entries.val[i]?

theorem universalFrame_refl (stack : Universals) : UniversalFrame stack stack := ⟨rfl, by simp⟩

theorem universalFrame_trans {a b c : Universals}
    (ab : UniversalFrame a b) (bc : UniversalFrame b c) : UniversalFrame a c := by
  refine ⟨bc.1.trans ab.1, ?_⟩
  intro i below
  exact (bc.2 i (by rw [ab.1]; exact below)).trans (ab.2 i below)

def UniversalPushPost (before : Universals) (id : U32) (work : Work)
    (answer : core.result.Result Unit fang_skolem_core.Error × Universals × Work) : Prop :=
  UniversalValid answer.2.1 ∧
  work.statistics.operations.val ≤ answer.2.2.statistics.operations.val ∧
  work.statistics.allocated_nodes.val ≤ answer.2.2.statistics.allocated_nodes.val ∧
  match answer.1 with
  | .Ok _ => answer.2.1.active.val = before.active.val + 1 ∧
      answer.2.1.entries.val = UniversalPushedEntries before id ∧
      answer.2.2.statistics.operations.val = work.statistics.operations.val + 1 ∧
      answer.2.2.statistics.allocated_nodes.val = work.statistics.allocated_nodes.val +
        (if before.active.val < before.entries.val.length then 0 else 1)
  | .Err error => answer.2.1 = before ∧
      match error with
      | .Resource kind => kind = .Operations ∨ kind = .StoredNodes
      | .Core _ => False

/-- A successful push preserves the old active prefix and adds exactly one ID.
    Capacity of the scalar active-depth counter is an explicit caller premise. -/
theorem universals_push_spec (stack : Universals) (id : U32) (limits : Limits) (work : Work)
    (valid : UniversalValid stack) (room : stack.active.val < Usize.max) :
    Universals.push stack id limits work ⦃ UniversalPushPost stack id work ⦄ := by
  unfold Universals.push
  apply spec_bind (tick_spec work limits)
  intro answer ticked
  unfold TickAnswer at ticked
  split at ticked
  next fits =>
    obtain ⟨operation, rfl, operation_eq⟩ := ticked
    simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    split
    next reuse =>
      have index_bound : stack.active.val < stack.entries.val.length := by scalar_tac
      rw [alloc.vec.Vec.index_mut_slice_index]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec stack.entries stack.active index_bound)
      rintro ⟨old, back⟩ ⟨old_eq, rfl⟩
      apply spec_bind (Usize.add_spec (x := stack.active) (y := 1#usize) (by scalar_tac))
      intro depth depth_eq
      simp only [spec_ok, UniversalPushPost]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [UniversalValid, alloc.vec.Vec.set_val_eq, List.length_set]
        scalar_tac
      · scalar_tac
      · exact Nat.le_refl _
      · scalar_tac
      · simp [UniversalPushedEntries, index_bound]
      · scalar_tac
      · simp [index_bound]
    next append_slot =>
      have at_end : stack.active.val = stack.entries.val.length := by
        unfold UniversalValid at valid
        scalar_tac
      apply spec_bind (allocate_spec _ 1#usize limits)
      intro answer allocated
      unfold AllocationAnswer at allocated
      split at allocated
      next storageFits =>
        obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
        simp only [Aeneas.Std.uncurry, bind_ok]
        apply spec_bind (alloc.vec.Vec.push_spec stack.entries id (by omega))
        intro entries entries_eq
        apply spec_bind (Usize.add_spec (x := stack.active) (y := 1#usize) (by scalar_tac))
        intro depth depth_eq
        simp only [spec_ok, UniversalPushPost]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [UniversalValid, entries_eq, List.length_append, List.length_singleton]
          scalar_tac
        · scalar_tac
        · scalar_tac
        · scalar_tac
        · simpa [UniversalPushedEntries, at_end] using entries_eq
        · scalar_tac
        · simpa [at_end] using nodes_eq
      next storageExceeded =>
        rw [allocated]
        have post : UniversalPushPost stack id work (.Err (.Resource .StoredNodes), stack,
            { statistics := { work.statistics with operations := operation } }) := by
          exact ⟨valid, by dsimp only; omega, Nat.le_refl _, rfl, Or.inr rfl⟩
        simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  next exceeded =>
    rw [ticked]
    simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      UniversalPushPost, valid]

theorem universals_pop_spec (stack : Universals) (valid : UniversalValid stack) :
    Universals.pop stack ⦃ fun after => UniversalValid after ∧
      after.active.val = stack.active.val - 1 ∧ after.entries = stack.entries ⦄ := by
  unfold Universals.pop
  split
  next positive =>
    apply spec_bind (Usize.sub_spec (x := stack.active) (y := 1#usize) (by scalar_tac))
    intro depth depth_eq
    simp only [spec_ok]
    refine ⟨?_, ?_, trivial⟩
    · unfold UniversalValid at valid ⊢
      dsimp only
      scalar_tac
    · scalar_tac
  next zero =>
    simp only [spec_ok]
    refine ⟨valid, ?_, trivial⟩
    scalar_tac

theorem universalPushedEntries_lower (stack : Universals) (id : U32) (index : Nat)
    (valid : UniversalValid stack) (below : index < stack.active.val) :
    (UniversalPushedEntries stack id)[index]? = stack.entries.val[index]? := by
  unfold UniversalPushedEntries
  split
  · simp [show index ≠ stack.active.val by omega]
  · have bound : index < stack.entries.val.length := by unfold UniversalValid at valid; omega
    simp [List.getElem?_append_left bound]

theorem universalPushedEntries_top (stack : Universals) (id : U32)
    (valid : UniversalValid stack) :
    (UniversalPushedEntries stack id)[stack.active.val]? = some id := by
  unfold UniversalPushedEntries
  split
  next inside => simp [inside]
  next outside =>
    have at_end : stack.active.val = stack.entries.val.length := by unfold UniversalValid at valid; omega
    simp [at_end]

/-- Pop restores the caller's frame even if a nested call reused inactive slots. -/
theorem universals_popped_frame (before pushed inner after : Universals) (id : U32)
    (valid : UniversalValid before)
    (pushed_depth : pushed.active.val = before.active.val + 1)
    (pushed_entries : pushed.entries.val = UniversalPushedEntries before id)
    (inner_frame : UniversalFrame pushed inner)
    (popped_depth : after.active.val = inner.active.val - 1)
    (popped_entries : after.entries = inner.entries) : UniversalFrame before after := by
  have inner_depth := inner_frame.1
  refine ⟨by omega, ?_⟩
  intro index below
  rw [popped_entries, inner_frame.2 index (by omega), pushed_entries]
  exact universalPushedEntries_lower before id index valid below

end FangSkolemCore
