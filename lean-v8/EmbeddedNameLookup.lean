/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedStack

set_option maxRecDepth 10000
open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

def NamePost (expected : Option U32) (before : Work)
    (answer : core.result.Result Bool fang_skolem_core.fang_quantified_fof_core.Error × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.statistics.operations.val ∧
    match answer.1 with
    | .Ok value => expected.isSome = value
    | .Err (.Resource kind) => kind = .Operations
    | .Err (.Invalid _) | .Err (.Unsupported _) => False

/-- The actual generated scope-membership lookup terminates, recognizes exactly
    the active bound names, and can fail only on the operation cap. -/
theorem bound_name_loop_spec (id : U32) (entries : alloc.vec.Vec Binding)
    (limits : Limits) (work : Work) (remaining : Usize)
    (bound : remaining.val ≤ entries.val.length) :
    bound_name_loop id entries limits work remaining
      ⦃ NamePost (lookupPrefix id entries.val remaining.val) work ⦄ := by
  unfold bound_name_loop
  split
  next positive =>
    apply spec_bind (tick_spec work limits)
    intro answer ticked
    unfold TickAnswer at ticked
    split at ticked
    next fits =>
      obtain ⟨operation, rfl, operation_eq⟩ := ticked
      have op_eq : operation.val = work.statistics.operations.val + 1 := by simpa using operation_eq
      simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (Usize.sub_spec (x := remaining) (y := 1#usize) (by scalar_tac))
      intro previous previous_eq
      have previous_bound : previous.val < entries.val.length := by scalar_tac
      have successor : remaining.val = previous.val + 1 := by scalar_tac
      rw [alloc.vec.Vec.index_slice_index]
      apply spec_bind (alloc.vec.Vec.index_usize_spec entries previous previous_bound)
      intro entry entry_eq
      subst entry
      have prefix_eq : lookupPrefix id entries.val remaining.val =
          if entries.val[previous.val].original = id then some entries.val[previous.val].fresh
          else lookupPrefix id entries.val previous.val := by
        rw [successor]
        simp only [lookupPrefix, List.getElem?_eq_getElem previous_bound]
      split
      next same_name =>
        simp only [spec_ok, NamePost]
        constructor
        · omega
        · rw [prefix_eq, ite_eq_left same_name]
          rfl
      next different =>
        apply spec_mono (bound_name_loop_spec id entries limits _ previous (by omega))
        rintro ⟨result, after⟩ ⟨monotone, checked⟩
        refine ⟨?_, ?_⟩
        · change work.statistics.operations.val ≤ after.statistics.operations.val
          change operation.val ≤ after.statistics.operations.val at monotone
          omega
        · rw [prefix_eq, ite_eq_right different]
          exact checked
    next exhausted =>
      subst answer
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, NamePost]
  next zero =>
    have empty : remaining.val = 0 := by scalar_tac
    simp [NamePost, empty, lookupPrefix]
termination_by remaining.val
decreasing_by omega

theorem bound_name_spec (id : U32) (stack : Bindings) (limits : Limits) (work : Work)
    (valid : StackValid stack) :
    bound_name id stack limits work
      ⦃ NamePost (lookupPrefix id stack.entries.val stack.active.val) work ⦄ :=
  bound_name_loop_spec id stack.entries limits work stack.active valid


end FangSkolemEmbeddedCore
