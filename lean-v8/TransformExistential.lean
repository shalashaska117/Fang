/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Actual fresh-symbol introduction, substitution and recursive continuation. -/
import TransformUniversal

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

theorem transform_existential_spec (before : Transformer) (binder : U32) (body : Nnf)
    (limits : Limits) (valid : UniversalValid before.universals)
    (ready : TransformReady (universalIds before.universals) (.Exists binder body))
    (bodyChecked : ∀ (state : Transformer) (replacement : fang.syntax.Term) (target : Nnf),
      UniversalValid state.universals →
      universalIds state.universals = universalIds before.universals →
      decodeTerm replacement = .app before.functions.val.length
        ((universalIds before.universals).map Fang.Term.var) →
      SubstitutedNnf binder replacement true body target →
      Transformer.transform state target limits ⦃ TransformPost state target ⦄) :
    Transformer.transform before (.Exists binder body) limits ⦃ TransformPost before (.Exists binder body) ⦄ := by
  unfold Transformer.transform
  apply spec_bind (tick_spec before.work limits)
  intro answer ticked
  unfold TickAnswer at ticked
  split at ticked
  next fits =>
    obtain ⟨operation, rfl, operation_eq⟩ := ticked
    simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    let advanced : Transformer := { before with work := { statistics := {
      before.work.statistics with operations := operation } } }
    apply spec_bind (introduce_spec advanced binder limits valid)
    rintro ⟨introducedResult, introduced⟩ introduction
    have savedIntroduction := introduction
    obtain ⟨sameStack, sameDeclaration, introducedOperations, introducedStorage, introducedOutcome⟩ := introduction
    dsimp only [advanced] at sameStack sameDeclaration introducedOperations introducedStorage introducedOutcome
    have introducedValid : UniversalValid introduced.universals := by rw [sameStack]; exact valid
    have introducedIds : universalIds introduced.universals = universalIds before.universals := by rw [sameStack]
    simp only [Aeneas.Std.uncurry]
    cases introducedResult with
    | Err error =>
      obtain ⟨sameFunctions, sameOrigins, failure⟩ := introducedOutcome
      have frame : UniversalFrame before.universals introduced.universals := by
        rw [sameStack]; exact universalFrame_refl _
      have post : TransformPost before (.Exists binder body) (.Err error, introduced) := by
        refine ⟨introducedValid, frame, sameDeclaration, by dsimp only; omega, ?_⟩
        cases error with
        | Core kind => exact failure
        | Resource kind => exact introduceResource_transform failure
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok replacement =>
      have replacementDecoded := introduce_decoded savedIntroduction
      dsimp only [advanced] at replacementDecoded
      obtain ⟨function, arguments, dependencies, termShape, functionId, argumentIds, dependencyIds,
        functionTable, origins, operationCount, storageCount⟩ := introducedOutcome
      have functionCount : introduced.functions.val.length = before.functions.val.length + 1 := by
        simp only [functionTable, List.length_append, List.length_singleton]
      simp only [bind_ok]
      apply spec_bind (substitute_nnf_total body binder replacement true limits introduced.work)
      rintro ⟨substitutedResult, substitutedWork⟩ ⟨substitutedOperations, substitutedOutcome⟩
      dsimp only at substitutedOperations substitutedOutcome
      simp only [Aeneas.Std.uncurry]
      cases substitutedResult with
      | Err error =>
        have frame : UniversalFrame before.universals introduced.universals := by
          rw [sameStack]; exact universalFrame_refl _
        have post : TransformPost before (.Exists binder body)
            (.Err error, { introduced with work := substitutedWork }) := by
          refine ⟨introducedValid, frame, sameDeclaration, by dsimp only; omega, ?_⟩
          cases error with
          | Core kind => exact substitutedOutcome
          | Resource kind => exact copyResource_transform substitutedOutcome
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
      | Ok target =>
        simp only [bind_ok]
        apply spec_mono (bodyChecked { introduced with work := substitutedWork } replacement target
          introducedValid introducedIds replacementDecoded substitutedOutcome)
        rintro ⟨result, after⟩ ⟨afterValid, afterFrame, afterDeclaration, afterOperations, afterOutcome⟩
        dsimp only at afterValid afterFrame afterDeclaration afterOperations afterOutcome
        rw [sameStack] at afterFrame
        refine ⟨afterValid, afterFrame, afterDeclaration.trans sameDeclaration, by dsimp only; omega, ?_⟩
        cases result with
        | Err error => exact afterOutcome
        | Ok output =>
          have substitutedDecoded := substituted_nnf_decode substitutedOutcome
          simp only [ite_true, replacementDecoded] at substitutedDecoded
          rw [introducedIds, functionCount, substitutedDecoded] at afterOutcome
          have safe := (transformReady_existential_substitution ready replacementDecoded substitutedOutcome).2
          rw [replacementDecoded] at safe
          exact .existential ready.1 safe afterOutcome
  next exceeded =>
    rw [ticked]
    have post := transformPost_resource before (.Exists binder body) before.work .Operations valid
      (Nat.le_refl _) (Or.inl rfl)
    simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post

end FangSkolemCore
