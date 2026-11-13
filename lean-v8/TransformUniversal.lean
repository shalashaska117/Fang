/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Actual universal push, recursive call and pop on both result branches. -/
import TransformBinary

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

theorem transform_universal_spec (before : Transformer) (binder : U32) (body : Nnf)
    (limits : Limits) (valid : UniversalValid before.universals)
    (room : before.universals.active.val < Usize.max)
    (bodyChecked : ∀ state : Transformer, UniversalValid state.universals →
      universalIds state.universals = universalIds before.universals ++ [binder.val] →
      Transformer.transform state body limits ⦃ TransformPost state body ⦄) :
    Transformer.transform before (.Forall binder body) limits ⦃ TransformPost before (.Forall binder body) ⦄ := by
  unfold Transformer.transform
  apply spec_bind (tick_spec before.work limits)
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
    next storageFits =>
      obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
      simp only [Aeneas.Std.uncurry, bind_ok]
      apply spec_bind (universals_push_spec before.universals binder limits _ valid room)
      rintro ⟨pushedResult, pushed, pushedWork⟩ ⟨pushedValid, pushedOperations, pushedStorage, pushedOutcome⟩
      dsimp only at pushedValid pushedOperations pushedStorage pushedOutcome
      simp only [Aeneas.Std.uncurry]
      cases pushedResult with
      | Err error =>
        obtain ⟨same, failure⟩ := pushedOutcome
        subst pushed
        have post : TransformPost before (.Forall binder body) (.Err error, { before with work := pushedWork }) := by
          refine ⟨valid, universalFrame_refl _, rfl, by dsimp only; omega, ?_⟩
          cases error with
          | Core kind => exact failure
          | Resource kind => rcases failure with same | same <;> simp [TransformFailure, TransformResource, same]
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
      | Ok returned =>
        obtain ⟨pushedDepth, pushedEntries, _, _⟩ := pushedOutcome
        have pushedIds := universals_pushed_ids binder valid pushedDepth pushedEntries
        simp only [bind_ok]
        apply spec_bind (bodyChecked { before with universals := pushed, work := pushedWork } pushedValid pushedIds)
        rintro ⟨bodyResult, inner⟩ ⟨innerValid, innerFrame, innerDeclaration, innerOperations, innerOutcome⟩
        dsimp only at innerValid innerFrame innerDeclaration innerOperations innerOutcome
        simp only [Aeneas.Std.uncurry]
        apply spec_bind (universals_pop_spec inner.universals innerValid)
        rintro popped ⟨poppedValid, poppedDepth, poppedEntries⟩
        have frame := universals_popped_frame before.universals pushed inner.universals popped binder
          valid pushedDepth pushedEntries innerFrame poppedDepth poppedEntries
        have operations : before.work.statistics.operations.val ≤ inner.work.statistics.operations.val := by omega
        cases bodyResult with
        | Err error =>
          have post : TransformPost before (.Forall binder body) (.Err error, { inner with universals := popped }) :=
            ⟨poppedValid, frame, innerDeclaration, operations, innerOutcome⟩
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
        | Ok target =>
          simp only [bind_ok, spec_ok, TransformPost]
          refine ⟨poppedValid, frame, innerDeclaration, operations, ?_⟩
          rw [pushedIds] at innerOutcome
          exact .universal innerOutcome
    next storageExceeded =>
      rw [allocated]
      have post := transformPost_resource before (.Forall binder body)
        { statistics := { before.work.statistics with operations := operation } } .StoredNodes valid
        (by dsimp only; omega) (Or.inr (Or.inl rfl))
      simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  next exceeded =>
    rw [ticked]
    have post := transformPost_resource before (.Forall binder body) before.work .Operations valid
      (Nat.le_refl _) (Or.inl rfl)
    simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post

end FangSkolemCore
