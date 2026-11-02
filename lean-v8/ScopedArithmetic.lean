/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Contracts over the actual Charon/Aeneas-generated Rust arithmetic boundary.
-/
import Fof

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core

def BoundedAnswer (left right cap : Usize) (kind : Resource)
    (result : core.result.Result Usize fang_fof_core.Error) : Prop :=
  if left.val + right.val ≤ cap.val then
    ∃ value, result = .Ok value ∧ value.val = left.val + right.val
  else result = .Err (.Resource kind)

/-- Total exact arithmetic with a typed capacity error and no arithmetic panic. -/
theorem bounded_add_spec (left right cap : Usize) (kind : Resource) :
    bounded_add left right cap kind ⦃ BoundedAnswer left right cap kind ⦄ := by
  unfold bounded_add
  split
  next exceeds =>
    simp only [spec_ok, BoundedAnswer]
    have outside : ¬ left.val + right.val ≤ cap.val := by scalar_tac
    simp [outside]
  next within =>
    apply spec_bind (Usize.sub_spec (x := cap) (y := left) (by scalar_tac))
    intro available subtracted
    split
    next exceeds =>
      simp only [spec_ok, BoundedAnswer]
      have outside : ¬ left.val + right.val ≤ cap.val := by scalar_tac
      simp [outside]
    next within =>
      apply spec_bind (Usize.add_spec (x := left) (y := right) (by scalar_tac))
      intro value added
      simp only [spec_ok, BoundedAnswer]
      rw [ite_eq_left (by scalar_tac)]
      exact ⟨value, rfl, by scalar_tac⟩

def ArithmeticAnswer (expected : Nat)
    (result : core.result.Result Usize fang_fof_core.Error) : Prop :=
  if expected ≤ Usize.max then
    ∃ value, result = .Ok value ∧ value.val = expected
  else result = .Err (.Resource .Arithmetic)

/-- Checked addition returns the exact natural sum or precisely arithmetic overflow. -/
theorem add_spec (left right : Usize) :
    add left right ⦃ ArithmeticAnswer (left.val + right.val) ⦄ := by
  have checked := Usize.checked_add_bv_spec left right
  unfold add
  cases computation : Usize.checked_add left right with
  | none =>
    simp only [computation] at checked
    have exceeds : ¬ left.val + right.val ≤ Usize.max := by omega
    simp [lift, core.option.Option.ok_or, ArithmeticAnswer, exceeds]
  | some value =>
    simp only [computation] at checked
    simpa [lift, core.option.Option.ok_or, ArithmeticAnswer, checked.1] using checked.2.1

/-- Checked multiplication returns the exact natural product or precisely arithmetic overflow. -/
theorem multiply_spec (left right : Usize) :
    multiply left right ⦃ ArithmeticAnswer (left.val * right.val) ⦄ := by
  have checked := Usize.checked_mul_bv_spec left right
  unfold multiply
  cases computation : Usize.checked_mul left right with
  | none =>
    simp only [computation] at checked
    have exceeds : ¬ left.val * right.val ≤ Usize.max := by omega
    simp [lift, core.option.Option.ok_or, ArithmeticAnswer, exceeds]
  | some value =>
    simp only [computation] at checked
    simpa [lift, core.option.Option.ok_or, ArithmeticAnswer, checked.1] using checked.2.1

def TickAnswer (before : Work) (limits : Limits)
    (answer : core.result.Result Unit fang_fof_core.Error × Work) : Prop :=
  if before.statistics.operations.val + 1 ≤ limits.max_operations.val then
    ∃ value, answer = (.Ok (), { statistics := { before.statistics with operations := value } }) ∧
      value.val = before.statistics.operations.val + 1
  else answer = (.Err (.Resource .Operations), before)

/-- A successful tick changes only operations; resource failure preserves Work. -/
theorem tick_spec (before : Work) (limits : Limits) :
    Work.tick before limits ⦃ TickAnswer before limits ⦄ := by
  unfold Work.tick
  apply spec_bind (bounded_add_spec before.statistics.operations 1#usize limits.max_operations .Operations)
  intro result checked
  unfold BoundedAnswer at checked
  split at checked
  next fits =>
    obtain ⟨value, rfl, value_eq⟩ := checked
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    simp only [spec_ok, TickAnswer]
    rw [ite_eq_left (by simpa using fits)]
    exact ⟨value, rfl, by simpa using value_eq⟩
  next exceeds =>
    rw [checked]
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      TickAnswer, show ¬ before.statistics.operations.val + 1 ≤ limits.max_operations.val by simpa using exceeds]

def AllocationAnswer (before : Work) (count : Usize) (limits : Limits)
    (answer : core.result.Result Unit fang_fof_core.Error × Work) : Prop :=
  if before.statistics.allocated_nodes.val + count.val ≤ limits.max_stored_nodes.val then
    ∃ value, answer = (.Ok (), { statistics := { before.statistics with allocated_nodes := value } }) ∧
      value.val = before.statistics.allocated_nodes.val + count.val
  else answer = (.Err (.Resource .StoredNodes), before)

/-- Allocation accounting changes only its count, or returns its exact typed error. -/
theorem allocate_spec (before : Work) (count : Usize) (limits : Limits) :
    Work.allocate before count limits ⦃ AllocationAnswer before count limits ⦄ := by
  unfold Work.allocate
  apply spec_bind (bounded_add_spec before.statistics.allocated_nodes count limits.max_stored_nodes .StoredNodes)
  intro result checked
  unfold BoundedAnswer at checked
  split at checked
  next fits =>
    obtain ⟨value, rfl, value_eq⟩ := checked
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    simp only [spec_ok, AllocationAnswer]
    rw [ite_eq_left fits]
    exact ⟨value, rfl, value_eq⟩
  next exceeds =>
    rw [checked]
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      AllocationAnswer, exceeds]

end FangScopedFof

#print axioms FangScopedFof.bounded_add_spec
#print axioms FangScopedFof.add_spec
#print axioms FangScopedFof.multiply_spec
#print axioms FangScopedFof.tick_spec
#print axioms FangScopedFof.allocate_spec
