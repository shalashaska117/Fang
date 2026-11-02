/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Scope

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core

def CopyResource (kind : Resource) : Prop := kind = .Operations ∨ kind = .StoredNodes

/-- Validated scoped copying can fail on resources, never with an invalid-input verdict. -/
def CopyPost {α : Type} (returned : α → Prop) (before : Work)
    (answer : core.result.Result α fang_fof_core.Error × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.statistics.operations.val ∧
    match answer.1 with
    | .Ok value => returned value
    | .Err (.Invalid _) => False
    | .Err (.Resource kind) => CopyResource kind

theorem copy_term_loop_spec (symbol : U32) (arguments : alloc.vec.Vec fang.syntax.Term)
    (limits : Limits)
    (child : ∀ i (h : i < arguments.val.length) work,
      copy_term arguments.val[i] limits work ⦃ CopyPost (fun value => value = arguments.val[i]) work ⦄)
    (work : Work) (copied : alloc.vec.Vec fang.syntax.Term) (index : Usize)
    (copied_prefix : copied.val = arguments.val.take index.val) :
    copy_term_loop symbol arguments limits work copied index
      ⦃ CopyPost (fun value => value = .Fun symbol arguments) work ⦄ := by
  unfold copy_term_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < arguments.val.length := by scalar_tac
    have hcopied : copied.val.length = index.val := by
      rw [copied_prefix, List.length_take]
      omega
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec arguments index hindex)
    intro term ht
    subst term
    apply spec_bind (child index.val hindex work)
    rintro ⟨answer, updated⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : CopyPost (fun value => value = fang.syntax.Term.Fun symbol arguments) work (.Err error, updated) := by
        refine ⟨hm, ?_⟩
        cases error with
        | Resource kind => exact hp
        | Invalid kind => exact hp
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok value =>
      subst value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (alloc.vec.Vec.push_spec copied arguments.val[index.val] (by
        have := arguments.property
        omega))
      intro extended extended_eq
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      intro next hn
      have hnval : next.val = index.val + 1 := by simpa using hn
      have prefix1 : extended.val = arguments.val.take next.val := by
        rw [extended_eq, copied_prefix, hnval]
        exact (List.take_succ_eq_append_getElem hindex).symm
      apply spec_mono (copy_term_loop_spec symbol arguments limits child updated extended next prefix1)
      rintro ⟨result, after⟩ ⟨hm2, hp2⟩
      exact ⟨by dsimp only at hm2 ⊢; omega, hp2⟩
  next hi =>
    have hindex : arguments.val.length ≤ index.val := by scalar_tac
    have same : copied = arguments := by
      apply alloc.vec.Vec.ext
      rw [copied_prefix, List.take_of_length_le hindex]
    simp [same, CopyPost]
termination_by arguments.val.length - index.val
decreasing_by omega

theorem copy_term_spec (term : fang.syntax.Term) {signature : Signature} {scope : VariableScope} (ground : TermValid signature scope term)
    (limits : Limits) (work : Work) :
    copy_term term limits work ⦃ CopyPost (fun value => value = term) work ⦄ := by
  induction ground generalizing work with
  | var id valid =>
    unfold copy_term
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
      next fitsAllocation =>
        obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
        simp only [Aeneas.Std.uncurry, bind_ok, spec_ok, CopyPost]
        exact ⟨by omega, trivial⟩
      next exceedsAllocation =>
        rw [allocated]
        simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          CopyPost, CopyResource] using (show work.statistics.operations.val ≤ operation.val by omega)
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource]
  | fun_ symbol arguments arity children ih =>
    unfold copy_term
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
      next fitsAllocation =>
        obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
        simp only [Aeneas.Std.uncurry, bind_ok]
        apply spec_mono (copy_term_loop_spec symbol arguments limits ih _ (alloc.vec.Vec.new _) 0#usize (by simp))
        rintro ⟨result, after⟩ ⟨hm, hp⟩
        exact ⟨by dsimp only at hm ⊢; omega, hp⟩
      next exceedsAllocation =>
        rw [allocated]
        simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          CopyPost, CopyResource] using (show work.statistics.operations.val ≤ operation.val by omega)
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource]

theorem copy_arguments_loop_spec (arguments : Slice fang.syntax.Term) (limits : Limits)
    {signature : Signature} {scope : VariableScope}
    (ground : ∀ i (h : i < arguments.val.length), TermValid signature scope arguments.val[i])
    (work : Work) (copied : alloc.vec.Vec fang.syntax.Term) (index : Usize)
    (copied_prefix : copied.val = arguments.val.take index.val) :
    copy_arguments_loop arguments limits work copied index
      ⦃ CopyPost (fun value => value.val = arguments.val) work ⦄ := by
  unfold copy_arguments_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < arguments.val.length := by scalar_tac
    have hcopied : copied.val.length = index.val := by
      rw [copied_prefix, List.length_take]
      omega
    apply spec_bind (Slice.index_usize_spec arguments index hindex)
    intro term ht
    subst term
    apply spec_bind (copy_term_spec arguments.val[index.val] (ground index.val hindex) limits work)
    rintro ⟨answer, updated⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : CopyPost (fun value : alloc.vec.Vec fang.syntax.Term => value.val = arguments.val)
          work (.Err error, updated) := by
        refine ⟨hm, ?_⟩
        cases error with
        | Resource kind => exact hp
        | Invalid kind => exact hp
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok value =>
      subst value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (alloc.vec.Vec.push_spec copied arguments.val[index.val] (by
        have := arguments.property
        omega))
      intro extended extended_eq
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      intro next hn
      have hnval : next.val = index.val + 1 := by simpa using hn
      have prefix1 : extended.val = arguments.val.take next.val := by
        rw [extended_eq, copied_prefix, hnval]
        exact (List.take_succ_eq_append_getElem hindex).symm
      apply spec_mono (copy_arguments_loop_spec arguments limits ground updated extended next prefix1)
      rintro ⟨result, after⟩ ⟨hm2, hp2⟩
      exact ⟨by dsimp only at hm2 ⊢; omega, hp2⟩
  next hi =>
    have hindex : arguments.val.length ≤ index.val := by scalar_tac
    simp [CopyPost, copied_prefix, List.take_of_length_le hindex]
termination_by arguments.val.length - index.val
decreasing_by omega

theorem copy_arguments_spec (arguments : Slice fang.syntax.Term) (limits : Limits)
    {signature : Signature} {scope : VariableScope}
    (ground : ∀ i (h : i < arguments.val.length), TermValid signature scope arguments.val[i]) (work : Work) :
    copy_arguments arguments limits work ⦃ CopyPost (fun value => value.val = arguments.val) work ⦄ := by
  exact copy_arguments_loop_spec arguments limits ground work (alloc.vec.Vec.new _) 0#usize (by simp)

end FangScopedFof
