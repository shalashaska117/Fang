/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Partial correctness for generated code: a property of every successful
   result. The checker uses a generated function only through an equation
   stating its successful result, so failures and divergence need no case. -/
import Aeneas

namespace FangNaming
open Aeneas Aeneas.Std Result

theorem bind_eq_ok {α β : Type} {m : Result α} {k : α → Result β} {value : β}
    (success : (m >>= k) = ok value) : ∃ a, m = ok a ∧ k a = ok value := by
  match matched : m.match with
  | .ok a =>
    have same := Result.match.isOk.mp matched
    subst same
    rw [bind_tc_ok] at success
    exact ⟨a, rfl, success⟩
  | .div =>
    have same := Result.match.isDiv.mp matched
    subst same
    rw [bind_tc_div] at success
    exact absurd success div_not_ok
  | .vis effect continuation =>
    have same := Result.match.isVis.mp matched
    subst same
    rw [bind_tc_vis] at success
    exact absurd success vis_not_ok

theorem std_bind_eq_ok {α β : Type} {m : Result α} {k : α → Result β} {value : β}
    (success : Std.bind m k = ok value) : ∃ a, m = ok a ∧ k a = ok value := by
  rw [← bind_tc_eq] at success
  exact bind_eq_ok success

theorem ok_eq_ok {α : Type} {a b : α} (same : (ok a : Result α) = ok b) : a = b :=
  Result.ok_injective same

theorem fail_eq_ok {α : Type} {error : Error} {value : α} (same : (fail error : Result α) = ok value) : False :=
  fail_not_ok same

end FangNaming
