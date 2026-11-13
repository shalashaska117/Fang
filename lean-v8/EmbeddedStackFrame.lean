/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedTermValidation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

/-- The active prefix is preserved; inactive storage may change. -/
def StackFrame (before after : Bindings) : Prop :=
  after.active.val = before.active.val ∧
  ∀ i, i < before.active.val → after.entries.val[i]? = before.entries.val[i]?

theorem stackFrame_refl (stack : Bindings) : StackFrame stack stack := ⟨rfl, by simp⟩

theorem stackFrame_trans {a b c : Bindings} (ab : StackFrame a b) (bc : StackFrame b c) :
    StackFrame a c := by
  refine ⟨bc.1.trans ab.1, ?_⟩
  intro i hi
  exact (bc.2 i (by rw [ab.1]; exact hi)).trans (ab.2 i hi)

theorem lookupPrefix_ext (id : U32) (left right : List Binding) (count : Nat)
    (same : ∀ i, i < count → left[i]? = right[i]?) :
    lookupPrefix id left count = lookupPrefix id right count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [lookupPrefix, same count (by omega)]
    cases h : right[count]? with
    | none => rfl
    | some value =>
      simp only
      rw [ih (fun i hi => same i (by omega))]

theorem stackFrame_lookup {before after : Bindings} (frame : StackFrame before after) (id : U32) :
    lookupPrefix id after.entries.val after.active.val =
      lookupPrefix id before.entries.val before.active.val := by
  rw [frame.1]
  exact lookupPrefix_ext id _ _ _ frame.2

theorem pushedEntries_lower (stack : Bindings) (binding : Binding) (i : Nat)
    (valid : StackValid stack) (below : i < stack.active.val) :
    (PushedEntries stack binding)[i]? = stack.entries.val[i]? := by
  unfold PushedEntries
  split
  · simp [show i ≠ stack.active.val by omega]
  · have hi : i < stack.entries.val.length := by unfold StackValid at valid; omega
    simp [List.getElem?_append_left hi]

theorem pushedEntries_top (stack : Bindings) (binding : Binding) (valid : StackValid stack) :
    (PushedEntries stack binding)[stack.active.val]? = some binding := by
  unfold PushedEntries
  split
  next inside => simp [inside]
  next outside =>
    have at_end : stack.active.val = stack.entries.val.length := by unfold StackValid at valid; omega
    simp [at_end]

theorem pushed_lookup (stack after : Bindings) (binding : Binding) (valid : StackValid stack)
    (depth : after.active.val = stack.active.val + 1)
    (entries : after.entries.val = PushedEntries stack binding) (id : U32) :
    lookupPrefix id after.entries.val after.active.val =
      if binding.original = id then some binding.fresh
      else lookupPrefix id stack.entries.val stack.active.val := by
  rw [depth, lookupPrefix, entries, pushedEntries_top stack binding valid]
  simp only
  rw [lookupPrefix_ext id _ _ _ (fun i hi => pushedEntries_lower stack binding i valid hi)]

theorem popped_frame (before pushed inner after : Bindings) (binding : Binding)
    (valid : StackValid before)
    (pushed_depth : pushed.active.val = before.active.val + 1)
    (pushed_entries : pushed.entries.val = PushedEntries before binding)
    (inner_frame : StackFrame pushed inner)
    (popped_depth : after.active.val = inner.active.val - 1)
    (popped_entries : after.entries = inner.entries) :
    StackFrame before after := by
  have inner_depth := inner_frame.1
  refine ⟨by omega, ?_⟩
  intro i hi
  rw [popped_entries, inner_frame.2 i (by omega), pushed_entries]
  exact pushedEntries_lower before binding i valid hi

end FangSkolemEmbeddedCore
