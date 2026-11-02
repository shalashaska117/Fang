/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import BinderRemoval

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangBinderRemovalCore
open fang_binder_removal_core

def IncrementPost (value cap : Usize) (kind : Resource)
    (answer : core.result.Result Usize fang_binder_removal_core.Error) : Prop :=
  if value.val < cap.val then
    ∃ next, answer = .Ok next ∧ next.val = value.val + 1
  else answer = .Err (.Resource kind)

theorem increment_spec (value cap : Usize) (kind : Resource) :
    increment value cap kind ⦃ IncrementPost value cap kind ⦄ := by
  unfold increment
  split
  next exhausted =>
    have full : ¬ value.val < cap.val := by scalar_tac
    simp [IncrementPost, full]
  next available =>
    apply spec_bind (Usize.add_spec (x := value) (y := 1#usize) (by scalar_tac))
    intro next added
    simp only [spec_ok, IncrementPost]
    rw [ite_eq_left (by scalar_tac)]
    exact ⟨next, rfl, by simpa using added⟩

end FangBinderRemovalCore
