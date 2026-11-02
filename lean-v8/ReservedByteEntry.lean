/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ReservedModels
import ReservedFunctionBounds
import EqualityPipeline

namespace FangQuantifiedEqualityInput
open Fang.QuantifiedCertificate FangQuantifiedPipeline

/-- The certificate refers to the actual prepared mixed order. MixedLayout
    accounts for clause-block positions and stable literal deduplication before
    conversion to built-in equality. No grouped-list input index is substituted. -/
theorem prepareInput_check_original_unsat {input maximum prepared limits output blocks ordinary equality}
    (inputRun : prepareInput input maximum = .ok prepared)
    (skolemRun : fang_skolem_core.skolemize_problem prepared.declarations prepared.signature limits = .ok (.Ok output))
    (steps : List.Forall₂ ActualClausificationStep output.formulas.val blocks)
    (layout : MixedLayout (numericDeclarations prepared.original.declarations) blocks ordinary)
    (converted : FangQuantifiedEquality.ActualProblemConversion prepared.reservation ordinary equality)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check equality certificate = .ok ()) :
    ¬ Fang.NamedQuantifiedEquality.Grammar.BytesSatisfiable (Fang.Source.Grammar.spelling input) := by
  obtain ⟨decoded, transported⟩ := prepareInput_runs inputRun
  apply Fang.QuantifiedEqualityFrontend.decode_original_unsat decoded
  rintro ⟨D, nonempty, original, holds⟩
  let : Nonempty D := nonempty
  obtain ⟨valid, slot, _, _, _⟩ := prepareInput_tables inputRun
  have originalHolds := (transport_models transported
    (Fang.EqualityBridge.reserveInterpretation prepared.original.equalityId original)).mp holds
  have reservedHolds :
      (retained (numericDeclarations prepared.original.declarations)).Models
        (Fang.EqualityBridge.reserveInterpretation prepared.reservation.equality.val original) ∧
      SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation prepared.reservation.equality.val original)
        prepared.declarations.val := by
    simpa only [slot] using originalHolds
  obtain ⟨extended, preserved, grouped⟩ := skolem_actual_problem_models skolemRun
    (retained (numericDeclarations prepared.original.declarations))
    (prepareInput_retained_below inputRun) blocks steps
    (Fang.EqualityBridge.reserveInterpretation prepared.reservation.equality.val original)
  have groupedModel := grouped.mpr reservedHolds
  have mixedModel : ordinary.Models extended := (mixedLayout_models layout extended).mpr
    ((FangQuantifiedPipeline.models_append extended _ _).mp groupedModel)
  have equalityModel := (FangQuantifiedEquality.actualProblem_models original extended
    prepared.reservation prepared.signature.functions.val.length valid preserved converted).mp mixedModel
  exact Fang.Equality.Ordered.check_unsat equality certificate accepted
    ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation original extended, equalityModel⟩

end FangQuantifiedEqualityInput
