/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedCnfCopy

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core
variable {signature : Signature} {scope : VariableScope}
set_option maxRecDepth 2048

/-- This is accounting monotonicity, not a statement about physical memory. -/
def AllocationMonotone {α : Type} (before : Work) (answer : α × Work) : Prop :=
  before.statistics.allocated_nodes.val ≤ answer.2.statistics.allocated_nodes.val

theorem copy_term_loop_allocation (symbol : U32) (arguments : alloc.vec.Vec fang.syntax.Term)
    (limits : Limits)
    (child : ∀ i (h : i < arguments.val.length) work,
      copy_term arguments.val[i] limits work ⦃ AllocationMonotone work ⦄)
    (work : Work) (copied : alloc.vec.Vec fang.syntax.Term) (index : Usize)
    (copied_length : copied.val.length = index.val) :
    copy_term_loop symbol arguments limits work copied index ⦃ AllocationMonotone work ⦄ := by
  unfold copy_term_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < arguments.val.length := by scalar_tac
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec arguments index hindex)
    intro term ht
    subst term
    apply spec_bind (child index.val hindex work)
    rintro ⟨answer, updated⟩ monotone
    dsimp only [AllocationMonotone] at monotone
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, AllocationMonotone] using monotone
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (alloc.vec.Vec.push_spec copied value (by have := arguments.property; omega))
      intro extended extended_eq
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize)
        (by have := arguments.property; change index.val + 1 ≤ Usize.max; omega))
      intro next hn
      have hnval : next.val = index.val + 1 := by simpa using hn
      have length1 : extended.val.length = next.val := by
        rw [extended_eq, List.length_append, List.length_singleton, copied_length]
        simpa using hn.symm
      apply spec_mono (copy_term_loop_allocation symbol arguments limits child updated extended next length1)
      rintro ⟨result, after⟩ monotone2
      exact Nat.le_trans monotone monotone2
  next hi => simp [AllocationMonotone]
termination_by arguments.val.length - index.val
decreasing_by omega

theorem copy_term_allocation (term : fang.syntax.Term) (ground : (TermValid signature scope) term)
    (limits : Limits) (work : Work) :
    copy_term term limits work ⦃ AllocationMonotone work ⦄ := by
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
        simp only [Aeneas.Std.uncurry, bind_ok, spec_ok, AllocationMonotone]
        dsimp only at nodes_eq ⊢
        omega
      next exceedsAllocation =>
        rw [allocated]
        simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, AllocationMonotone]
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, AllocationMonotone]
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
        apply spec_mono (copy_term_loop_allocation symbol arguments limits ih _ (alloc.vec.Vec.new _) 0#usize (by simp))
        rintro ⟨result, after⟩ monotone
        dsimp only [AllocationMonotone] at monotone ⊢
        dsimp only at nodes_eq
        omega
      next exceedsAllocation =>
        rw [allocated]
        simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, AllocationMonotone]
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, AllocationMonotone]

theorem copy_arguments_loop_allocation (arguments : Slice fang.syntax.Term) (limits : Limits)
    (ground : ∀ i (h : i < arguments.val.length), (TermValid signature scope) arguments.val[i])
    (work : Work) (copied : alloc.vec.Vec fang.syntax.Term) (index : Usize)
    (copied_length : copied.val.length = index.val) :
    copy_arguments_loop arguments limits work copied index ⦃ AllocationMonotone work ⦄ := by
  unfold copy_arguments_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < arguments.val.length := by scalar_tac
    apply spec_bind (Slice.index_usize_spec arguments index hindex)
    intro term ht
    subst term
    apply spec_bind (copy_term_allocation arguments.val[index.val] (ground index.val hindex) limits work)
    rintro ⟨answer, updated⟩ monotone
    dsimp only [AllocationMonotone] at monotone
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, AllocationMonotone] using monotone
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (alloc.vec.Vec.push_spec copied value (by have := arguments.property; omega))
      intro extended extended_eq
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize)
        (by have := arguments.property; change index.val + 1 ≤ Usize.max; omega))
      intro next hn
      have hnval : next.val = index.val + 1 := by simpa using hn
      have length1 : extended.val.length = next.val := by
        rw [extended_eq, List.length_append, List.length_singleton, copied_length]
        simpa using hn.symm
      apply spec_mono (copy_arguments_loop_allocation arguments limits ground updated extended next length1)
      rintro ⟨result, after⟩ monotone2
      exact Nat.le_trans monotone monotone2
  next hi => simp [AllocationMonotone]
termination_by arguments.val.length - index.val
decreasing_by omega

theorem copy_arguments_allocation (arguments : Slice fang.syntax.Term) (limits : Limits)
    (ground : ∀ i (h : i < arguments.val.length), (TermValid signature scope) arguments.val[i]) (work : Work) :
    copy_arguments arguments limits work ⦃ AllocationMonotone work ⦄ := by
  exact copy_arguments_loop_allocation arguments limits ground work (alloc.vec.Vec.new _) 0#usize (by simp)

def LiteralAllocationPost (before : Work)
    (answer : core.result.Result fang.syntax.Literal fang_fof_core.Error × Work) : Prop :=
  AllocationMonotone before answer ∧ match answer.1 with
  | .Ok _ => before.statistics.allocated_nodes.val + 1 ≤ answer.2.statistics.allocated_nodes.val
  | .Err _ => True

/-- Successful literal copying accounts for its literal node before copying arguments. -/
theorem copy_literal_allocation (literal : fang.syntax.Literal) (ground : (LiteralScoped signature scope) literal)
    (limits : Limits) (work : Work) :
    copy_literal literal limits work ⦃ LiteralAllocationPost work ⦄ := by
  unfold copy_literal
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
      apply spec_bind (copy_arguments_allocation (alloc.vec.Vec.deref literal.arguments) limits
        (by simpa [alloc.vec.Vec.deref, LiteralScoped] using ground) _)
      rintro ⟨result, after⟩ monotone
      dsimp only [AllocationMonotone] at monotone
      dsimp only at nodes_eq
      have grown : nodes.val = work.statistics.allocated_nodes.val + 1 := by simpa using nodes_eq
      cases result <;>
        simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          LiteralAllocationPost, AllocationMonotone] <;> omega
    next exceedsAllocation =>
      rw [allocated]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        LiteralAllocationPost, AllocationMonotone]
  next exceedsOperations =>
    rw [ticked]
    simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      LiteralAllocationPost, AllocationMonotone]

end FangScopedFof
