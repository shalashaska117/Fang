/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedCnfProduct

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core
variable {signature : Signature} {scope : VariableScope}
set_option maxRecDepth 2048

def CnfResource (kind : Resource) : Prop :=
  CopyResource kind ∨ kind = .Clauses ∨ kind = .LiteralsPerClause ∨
    kind = .Literals ∨ kind = .Arithmetic

def CnfChecked {α : Type} (returned : α → Prop)
    (answer : core.result.Result α fang_fof_core.Error) : Prop :=
  match answer with
  | .Ok value => returned value
  | .Err (.Invalid _) => False
  | .Err (.Resource kind) => CnfResource kind

def CnfPost {α : Type} (returned : α → Prop) (before : Work)
    (answer : core.result.Result α fang_fof_core.Error × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.statistics.operations.val ∧ CnfChecked returned answer.1

theorem checked_add_spec (left right : Usize) :
    add left right ⦃ CnfChecked (fun value => value.val = left.val + right.val) ⦄ := by
  apply spec_mono (add_spec left right)
  intro answer post
  unfold ArithmeticAnswer at post
  split at post
  next fits => obtain ⟨value, rfl, eq⟩ := post; exact eq
  next exceeds => rw [post]; simp [CnfChecked, CnfResource]

theorem checked_multiply_spec (left right : Usize) :
    multiply left right ⦃ CnfChecked (fun value => value.val = left.val * right.val) ⦄ := by
  apply spec_mono (multiply_spec left right)
  intro answer post
  unfold ArithmeticAnswer at post
  split at post
  next fits => obtain ⟨value, rfl, eq⟩ := post; exact eq
  next exceeds => rw [post]; simp [CnfChecked, CnfResource]

theorem cnf_checked_bind {α β : Type} (computation : Result (core.result.Result α fang_fof_core.Error))
    (next : α → Result (core.result.Result β fang_fof_core.Error × Work))
    (property : α → Prop) (returned : β → Prop) (work : Work)
    (checked : computation ⦃ CnfChecked property ⦄)
    (continued : ∀ value, property value → next value ⦃ CnfPost returned work ⦄) :
    (do
      let answer ← computation
      let cf ← core.result.Result.Insts.CoreOpsTry.branch answer
      match cf with
      | core.ops.control_flow.ControlFlow.Continue value => next value
      | core.ops.control_flow.ControlFlow.Break residual =>
        let error ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          β (core.convert.FromSame fang_fof_core.Error) residual
        ok (error, work)) ⦃ CnfPost returned work ⦄ := by
  apply spec_bind checked
  intro answer hp
  cases answer with
  | Ok value =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch] using continued value hp
  | Err error =>
    have post : CnfPost returned work (.Err error, work) := by
      refine ⟨Nat.le_refl _, ?_⟩
      cases error <;> exact hp
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post

theorem check_shape_spec (clauses literals width : Usize) (limits : Limits) :
    check_shape clauses literals width limits ⦃ CnfChecked (fun _ =>
      clauses.val ≤ limits.max_clauses.val ∧ width.val ≤ limits.max_literals_per_clause.val ∧
      literals.val ≤ limits.max_literals.val) ⦄ := by
  unfold check_shape
  split
  · simp [CnfChecked, CnfResource]
  · split
    · simp [CnfChecked, CnfResource]
    · split
      · simp [CnfChecked, CnfResource]
      · simp only [spec_ok, CnfChecked]
        scalar_tac

theorem check_storage_spec (clauses literals terms : Usize) (limits : Limits) (work : Work) :
    check_storage clauses literals terms limits work ⦃ CnfChecked (fun _ =>
      work.statistics.allocated_nodes.val + clauses.val + literals.val + terms.val ≤ limits.max_stored_nodes.val) ⦄ := by
  unfold check_storage
  apply spec_bind (checked_add_spec clauses literals)
  intro answer hp
  cases answer with
  | Err error => cases error <;> simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfChecked] using hp
  | Ok count =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (checked_add_spec count terms)
    intro answer hp2
    cases answer with
    | Err error => cases error <;> simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfChecked] using hp2
    | Ok total =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (bounded_add_spec work.statistics.allocated_nodes total limits.max_stored_nodes .StoredNodes)
      intro answer bounded
      unfold BoundedAnswer at bounded
      split at bounded
      next fits =>
        obtain ⟨value, rfl, heq⟩ := bounded
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, spec_ok, CnfChecked]
        dsimp only [CnfChecked] at hp hp2
        omega
      next exceeds =>
        rw [bounded]
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfChecked, CnfResource, CopyResource]

end FangScopedFof
