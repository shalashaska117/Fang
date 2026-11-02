/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Contracts over the actual Charon/Aeneas-generated Rust arithmetic boundary.
-/
import Skolem

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

def BoundedAnswer (left right cap : Usize) (kind : Resource)
    (result : core.result.Result Usize fang_skolem_core.Error) : Prop :=
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

def TickAnswer (before : Work) (limits : Limits)
    (answer : core.result.Result Unit fang_skolem_core.Error × Work) : Prop :=
  if before.statistics.operations.val + 1 ≤ limits.core.max_operations.val then
    ∃ value, answer = (.Ok (), { statistics := { before.statistics with operations := value } }) ∧
      value.val = before.statistics.operations.val + 1
  else answer = (.Err (.Resource .Operations), before)

/-- A successful tick changes only operations; resource failure preserves Work. -/
theorem tick_spec (before : Work) (limits : Limits) :
    Work.tick before limits ⦃ TickAnswer before limits ⦄ := by
  unfold Work.tick
  apply spec_bind (bounded_add_spec before.statistics.operations 1#usize limits.core.max_operations .Operations)
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
      TickAnswer, show ¬ before.statistics.operations.val + 1 ≤ limits.core.max_operations.val by simpa using exceeds]

def AllocationAnswer (before : Work) (count : Usize) (limits : Limits)
    (answer : core.result.Result Unit fang_skolem_core.Error × Work) : Prop :=
  if before.statistics.allocated_nodes.val + count.val ≤ limits.core.max_stored_nodes.val then
    ∃ value, answer = (.Ok (), { statistics := { before.statistics with allocated_nodes := value } }) ∧
      value.val = before.statistics.allocated_nodes.val + count.val
  else answer = (.Err (.Resource .StoredNodes), before)

/-- Allocation accounting changes only its count, or returns its exact typed error. -/
theorem allocate_spec (before : Work) (count : Usize) (limits : Limits) :
    Work.allocate before count limits ⦃ AllocationAnswer before count limits ⦄ := by
  unfold Work.allocate
  apply spec_bind (bounded_add_spec before.statistics.allocated_nodes count limits.core.max_stored_nodes .StoredNodes)
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

/-- Remaining credits are exact, with every other core limit unchanged. The
    caller's counter bounds are explicit; translation alone does not prove them. -/
theorem remaining_spec (before : Work) (limits : Limits)
    (operations : before.statistics.operations.val ≤ limits.core.max_operations.val)
    (storage : before.statistics.allocated_nodes.val ≤ limits.core.max_stored_nodes.val) :
    Work.remaining before limits ⦃ fun result =>
      ∃ op nodes, result = { limits.core with max_operations := op, max_stored_nodes := nodes } ∧
        op.val + before.statistics.operations.val = limits.core.max_operations.val ∧
        nodes.val + before.statistics.allocated_nodes.val = limits.core.max_stored_nodes.val ⦄ := by
  unfold Work.remaining
  apply spec_bind (Usize.sub_spec (x := limits.core.max_operations)
    (y := before.statistics.operations) (by scalar_tac))
  intro op op_eq
  apply spec_bind (Usize.sub_spec (x := limits.core.max_stored_nodes)
    (y := before.statistics.allocated_nodes) (by scalar_tac))
  intro nodes nodes_eq
  simp only [spec_ok]
  exact ⟨op, nodes, rfl, by scalar_tac, by scalar_tac⟩

end FangSkolemCore

