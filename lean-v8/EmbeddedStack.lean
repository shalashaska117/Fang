/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Direct contracts over the unchanged quantified Rust extraction. -/
import EmbeddedArithmetic

set_option maxRecDepth 10000

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

def StackValid (stack : Bindings) : Prop := stack.active.val ≤ stack.entries.val.length

/-- The last matching entry in the active prefix. Inactive slots are ignored. -/
def lookupPrefix (id : U32) (entries : List Binding) : Nat → Option U32
  | 0 => none
  | count + 1 =>
      match entries[count]? with
      | none => none
      | some binding => if binding.original = id then some binding.fresh else lookupPrefix id entries count

theorem bindings_new_spec :
    Bindings.new ⦃ fun stack => StackValid stack ∧ stack.active.val = 0 ∧ stack.entries.val = [] ⦄ := by
  simp [Bindings.new, StackValid]

/-- Pop restores logical depth without observing or modifying inactive slots. -/
theorem bindings_pop_spec (stack : Bindings) (valid : StackValid stack) :
    Bindings.pop stack ⦃ fun after => StackValid after ∧
      after.active.val = stack.active.val - 1 ∧ after.entries = stack.entries ⦄ := by
  unfold Bindings.pop
  split
  next positive =>
    apply spec_bind (Usize.sub_spec (x := stack.active) (y := 1#usize) (by scalar_tac))
    intro depth hdepth
    simp only [spec_ok]
    refine ⟨?_, ?_, trivial⟩
    · unfold StackValid at valid ⊢
      dsimp only
      scalar_tac
    · scalar_tac
  next zero =>
    simp only [spec_ok]
    refine ⟨valid, ?_, trivial⟩
    scalar_tac

def PushedEntries (stack : Bindings) (value : Binding) : List Binding :=
  if stack.active.val < stack.entries.val.length then
    stack.entries.val.set stack.active.val value
  else stack.entries.val ++ [value]

/-- Push either reuses the first inactive slot or appends one slot, and preserves
    the active-depth invariant. The caller must leave one representable ID. -/
theorem bindings_push_spec (stack : Bindings) (value : Binding)
    (valid : StackValid stack) (room : stack.active.val < Usize.max) :
    Bindings.push stack value ⦃ fun after => StackValid after ∧
      after.active.val = stack.active.val + 1 ∧ after.entries.val = PushedEntries stack value ⦄ := by
  unfold Bindings.push
  dsimp only
  split
  next reuse =>
    have index_bound : stack.active.val < stack.entries.val.length := by scalar_tac
    have replace_spec : (do
        let (_, back) ← alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Binding)
          stack.entries stack.active
        ok (back value)) ⦃ fun updated => updated = stack.entries.set stack.active value ⦄ := by
      rw [alloc.vec.Vec.index_mut_slice_index]
      apply spec_bind (alloc.vec.Vec.index_mut_usize_spec stack.entries stack.active index_bound)
      rintro ⟨old, back⟩ ⟨old_eq, rfl⟩
      simp
    apply spec_bind replace_spec
    intro entries entries_eq
    subst entries
    apply spec_bind (Usize.add_spec (x := stack.active) (y := 1#usize) (by scalar_tac))
    intro depth depth_eq
    simp only [spec_ok]
    refine ⟨?_, ?_, ?_⟩
    · simp only [StackValid, alloc.vec.Vec.set_val_eq, List.length_set]
      scalar_tac
    · scalar_tac
    · simp [PushedEntries, index_bound]
  next append_slot =>
    have at_end : stack.active.val = stack.entries.val.length := by
      unfold StackValid at valid
      scalar_tac
    apply spec_bind (alloc.vec.Vec.push_spec stack.entries value (by omega))
    intro entries entries_eq
    apply spec_bind (Usize.add_spec (x := stack.active) (y := 1#usize) (by scalar_tac))
    intro depth depth_eq
    simp only [spec_ok]
    refine ⟨?_, ?_, ?_⟩
    · simp only [StackValid, entries_eq, List.length_append, List.length_singleton]
      scalar_tac
    · scalar_tac
    · simpa [PushedEntries, at_end] using entries_eq

def LookupPost (expected : Option U32) (before : Work)
    (answer : core.result.Result U32 fang_skolem_core.fang_quantified_fof_core.Error × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.statistics.operations.val ∧
    match answer.1 with
    | .Ok value => expected = some value
    | .Err (.Invalid kind) => kind = .FreeVariable ∧ expected = none
    | .Err (.Resource kind) => kind = .Operations
    | .Err (.Unsupported _) => False

/-- Actual generated reverse lookup terminates and returns the exact nearest
    binding, FreeVariable iff no binding exists, or an operation-cap error. -/
theorem lookup_binding_loop_spec (id : U32) (entries : alloc.vec.Vec Binding)
    (limits : Limits) (work : Work) (remaining : Usize)
    (bound : remaining.val ≤ entries.val.length) :
    lookup_binding_loop id entries limits work remaining
      ⦃ LookupPost (lookupPrefix id entries.val remaining.val) work ⦄ := by
  unfold lookup_binding_loop
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
        simp only [spec_ok, LookupPost]
        constructor
        · omega
        · rw [prefix_eq, ite_eq_left same_name]
      next different =>
        apply spec_mono (lookup_binding_loop_spec id entries limits _ previous (by omega))
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
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, LookupPost]
  next zero =>
    have empty : remaining.val = 0 := by scalar_tac
    simp [LookupPost, empty, lookupPrefix]
termination_by remaining.val
decreasing_by omega

theorem lookup_binding_spec (id : U32) (stack : Bindings) (limits : Limits) (work : Work)
    (valid : StackValid stack) :
    lookup_binding id stack limits work
      ⦃ LookupPost (lookupPrefix id stack.entries.val stack.active.val) work ⦄ :=
  lookup_binding_loop_spec id stack.entries limits work stack.active valid

end FangSkolemEmbeddedCore
