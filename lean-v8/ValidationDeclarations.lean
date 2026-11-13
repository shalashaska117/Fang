/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Validation of the actual generated declaration loop with shared credits. -/
import EmbeddedPublicValidation
import Absorb

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

def DeclarationValid (signature : fang_quantified_fof_core.Signature)
    (declaration : Declaration) : Prop :=
  FangSkolemEmbeddedCore.FormulaValid signature (fun _ => False) declaration.formula

def DeclarationsFrom (signature : fang_quantified_fof_core.Signature)
    (declarations : Slice Declaration) (start : Nat) : Prop :=
  ∀ i, start ≤ i → (inside : i < declarations.val.length) →
    DeclarationValid signature declarations.val[i]

def InvalidDeclarationFrom (signature : fang_quantified_fof_core.Signature)
    (declarations : Slice Declaration) (start : Nat) : Prop :=
  ∃ i, start ≤ i ∧ ∃ inside : i < declarations.val.length,
    ¬ DeclarationValid signature declarations.val[i]

def ValidationCounters (limits : Limits) (before after : Work) : Prop :=
  before.statistics.operations.val ≤ after.statistics.operations.val ∧
  before.statistics.allocated_nodes.val ≤ after.statistics.allocated_nodes.val ∧
  after.statistics.operations.val ≤ limits.core.max_operations.val ∧
  after.statistics.allocated_nodes.val ≤ limits.core.max_stored_nodes.val

theorem validationCounters_refl (limits : Limits) (work : Work)
    (operations : work.statistics.operations.val ≤ limits.core.max_operations.val)
    (storage : work.statistics.allocated_nodes.val ≤ limits.core.max_stored_nodes.val) :
    ValidationCounters limits work work := ⟨Nat.le_refl _, Nat.le_refl _, operations, storage⟩

theorem validationCounters_trans {limits : Limits} {before middle after : Work}
    (first : ValidationCounters limits before middle)
    (second : ValidationCounters limits middle after) :
    ValidationCounters limits before after :=
  ⟨Nat.le_trans first.1 second.1, Nat.le_trans first.2.1 second.2.1,
    second.2.2.1, second.2.2.2⟩

def ValidationDeclarationsOutcome (signature : fang_quantified_fof_core.Signature)
    (declarations : Slice Declaration) (start : Nat)
    (answer : core.result.Result Unit fang_skolem_core.Error) : Prop :=
  match answer with
  | .Ok _ => DeclarationsFrom signature declarations start
  | .Err (.Core (.Invalid _)) => InvalidDeclarationFrom signature declarations start
  | .Err (.Core (.Resource kind)) => FangSkolemEmbeddedCore.FormulaResource kind
  | .Err (.Core (.Unsupported _)) => False
  | .Err (.Resource kind) => kind = .Operations ∨ kind = .StoredNodes

def ValidationDeclarationsPost (signature : fang_quantified_fof_core.Signature)
    (declarations : Slice Declaration) (start : Nat) (limits : Limits) (before : Work)
    (answer : core.result.Result Unit fang_skolem_core.Error × Work) : Prop :=
  ValidationCounters limits before answer.2 ∧
    ValidationDeclarationsOutcome signature declarations start answer.1

theorem validationOutcome_previous {signature : fang_quantified_fof_core.Signature}
    {declarations : Slice Declaration} {index : Nat} (inside : index < declarations.val.length)
    (head : DeclarationValid signature declarations.val[index])
    {answer : core.result.Result Unit fang_skolem_core.Error}
    (tail : ValidationDeclarationsOutcome signature declarations (index + 1) answer) :
    ValidationDeclarationsOutcome signature declarations index answer := by
  cases answer with
  | Ok value =>
    intro i lower upper
    by_cases same : i = index
    · subst i; exact head
    · exact tail i (by omega) upper
  | Err error =>
    cases error with
    | Resource kind => exact tail
    | Core error =>
      cases error with
      | Resource kind => exact tail
      | Unsupported kind => exact tail
      | Invalid kind =>
        obtain ⟨i, lower, upper, invalid⟩ := tail
        exact ⟨i, by omega, upper, invalid⟩

/-- Absorbing a completed validator's counters is total even when that reported
    count exceeds the remaining credits. Only the two outer credit errors occur. -/
theorem absorb_validation_spec (work : Work)
    (statistics : fang_quantified_fof_core.Statistics) (limits : Limits)
    (operations : work.statistics.operations.val ≤ limits.core.max_operations.val)
    (storage : work.statistics.allocated_nodes.val ≤ limits.core.max_stored_nodes.val) :
    Work.absorb work statistics limits ⦃ fun answer =>
      ValidationCounters limits work answer.2 ∧
      match answer.1 with
      | .Ok _ => True
      | .Err (.Resource kind) => kind = .Operations ∨ kind = .StoredNodes
      | .Err (.Core _) => False ⦄ := by
  apply spec_mono (absorb_spec work statistics limits)
  intro answer checked
  unfold AbsorbPost at checked
  split at checked
  next fits =>
    obtain ⟨op, op_eq, allocated⟩ := checked
    unfold AllocationAnswer at allocated
    split at allocated
    next storageFits =>
      obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
      dsimp only at nodes_eq storageFits
      exact ⟨⟨by dsimp only; omega, by dsimp only; omega,
        by dsimp only; omega, by dsimp only; omega⟩, trivial⟩
    next exceeds =>
      rw [allocated]
      exact ⟨⟨by dsimp only; omega, Nat.le_refl _, by dsimp only; omega, storage⟩, Or.inr rfl⟩
  next exceeds =>
    rw [checked]
    exact ⟨validationCounters_refl limits work operations storage, Or.inl rfl⟩

theorem validate_declarations_loop_spec (declarations : Slice Declaration)
    (signature : fang_quantified_fof_core.Signature) (limits : Limits)
    (work : Work) (index : Usize)
    (operations : work.statistics.operations.val ≤ limits.core.max_operations.val)
    (storage : work.statistics.allocated_nodes.val ≤ limits.core.max_stored_nodes.val) :
    validate_declarations_loop declarations signature limits work index
      ⦃ ValidationDeclarationsPost signature declarations index.val limits work ⦄ := by
  unfold validate_declarations_loop
  dsimp only
  split
  next more =>
    have hi : index.val < declarations.val.length := by scalar_tac
    apply spec_bind (tick_spec work limits)
    intro answer ticked
    unfold TickAnswer at ticked
    split at ticked
    next fits =>
      obtain ⟨operation, rfl, operation_eq⟩ := ticked
      let tickedWork : Work := {statistics := {work.statistics with operations := operation}}
      have tickCounters : ValidationCounters limits work tickedWork :=
        ⟨by dsimp [tickedWork]; omega, Nat.le_refl _, by dsimp [tickedWork]; omega, storage⟩
      simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (Slice.index_usize_spec declarations index hi)
      intro declaration same
      subst declaration
      apply spec_bind (remaining_spec tickedWork limits tickCounters.2.2.1 tickCounters.2.2.2)
      intro remaining remaining_eq
      apply spec_bind (FangSkolemEmbeddedCore.validate_closed_spec declarations.val[index.val].formula signature remaining)
      intro validated checked
      cases validated with
      | Err error =>
        have post : ValidationDeclarationsPost signature declarations index.val limits work
            (.Err (.Core error), tickedWork) := by
          refine ⟨tickCounters, ?_⟩
          cases error with
          | Invalid kind => exact ⟨index.val, Nat.le_refl _, hi, checked⟩
          | Resource kind => exact checked
          | Unsupported kind => exact checked
        simpa [core.result.Result.map_err, P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
          Error.Core.constructor, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
      | Ok statistics =>
        simp only [core.result.Result.map_err, bind_ok]
        apply spec_bind (absorb_validation_spec tickedWork statistics limits
          tickCounters.2.2.1 tickCounters.2.2.2)
        rintro ⟨answer, after⟩ ⟨counters, outcome⟩
        have composed := validationCounters_trans tickCounters counters
        simp only [Aeneas.Std.uncurry]
        cases answer with
        | Err error =>
          have post : ValidationDeclarationsPost signature declarations index.val limits work
              (.Err error, after) := by
            refine ⟨composed, ?_⟩
            cases error with
            | Resource kind => exact outcome
            | Core error => exact False.elim outcome
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
        | Ok value =>
          simp only [bind_ok]
          apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
          intro next next_eq
          have nextval : next.val = index.val + 1 := by simpa using next_eq
          apply spec_mono (validate_declarations_loop_spec declarations signature limits after next
            composed.2.2.1 composed.2.2.2)
          rintro ⟨answer, final⟩ ⟨finalCounters, tail⟩
          refine ⟨validationCounters_trans composed finalCounters, ?_⟩
          rw [nextval] at tail
          exact validationOutcome_previous hi checked tail
    next exceeded =>
      rw [ticked]
      have post : ValidationDeclarationsPost signature declarations index.val limits work
          (.Err (.Resource .Operations), work) :=
        ⟨validationCounters_refl limits work operations storage, Or.inl rfl⟩
      simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  next done =>
    have last : declarations.val.length ≤ index.val := by scalar_tac
    simp only [spec_ok]
    refine ⟨validationCounters_refl limits work operations storage, ?_⟩
    intro i lower upper
    omega
termination_by declarations.val.length - index.val
decreasing_by scalar_tac

theorem validate_declarations_spec (declarations : Slice Declaration)
    (signature : fang_quantified_fof_core.Signature) (limits : Limits) (work : Work)
    (operations : work.statistics.operations.val ≤ limits.core.max_operations.val)
    (storage : work.statistics.allocated_nodes.val ≤ limits.core.max_stored_nodes.val) :
    validate_declarations declarations signature limits work
      ⦃ ValidationDeclarationsPost signature declarations 0 limits work ⦄ := by
  exact validate_declarations_loop_spec declarations signature limits work 0#usize operations storage

theorem validate_declarations_success {declarations : Slice Declaration}
    {signature : fang_quantified_fof_core.Signature} {limits : Limits} {before after : Work}
    (operations : before.statistics.operations.val ≤ limits.core.max_operations.val)
    (storage : before.statistics.allocated_nodes.val ≤ limits.core.max_stored_nodes.val)
    (success : validate_declarations declarations signature limits before = .ok (.Ok (), after)) :
    DeclarationsFrom signature declarations 0 ∧ ValidationCounters limits before after := by
  have checked := validate_declarations_spec declarations signature limits before operations storage
  rw [success] at checked
  simp only [spec_ok, ValidationDeclarationsPost, ValidationDeclarationsOutcome] at checked
  exact ⟨checked.2, checked.1⟩

end FangSkolemCore
