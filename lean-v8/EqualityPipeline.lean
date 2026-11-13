/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ClauseConversion
import InputScope

open Aeneas.Std

namespace FangQuantifiedEquality
open fang_fof_equality_bridge FangQuantifiedPipeline FangSkolemCore

/-- Successful extracted preprocessing and complete ordered clause conversion
    admit an equality interpretation for every nonempty original model.
    The original model interprets the reserved predicate as domain equality.
    Binding that slot and its table to original source bytes is a separate
    caller obligation; ValidReservation alone does not establish that binding. -/
theorem actual_preprocessing_models
    {declarations : Slice fang_skolem_core.Declaration}
    {signature : fang_skolem_core.fang_quantified_fof_core.Signature}
    {limits : fang_skolem_core.Limits} {output : fang_skolem_core.Skolemized}
    (success : fang_skolem_core.skolemize_problem declarations signature limits = .ok (.Ok output))
    (retained : Fang.Problem) (originalFunctions : ProblemBelow signature.functions.val.length retained)
    (blocks : List Fang.Problem)
    (steps : List.Forall₂ ActualClausificationStep output.formulas.val blocks)
    (reservation : Reservation) (valid : FangEqualityBridge.ValidReservation reservation)
    (equality : Fang.Equality.Problem)
    (converted : ActualProblemConversion reservation (retained ++ blocks.flatten) equality)
    {D : Type} [Nonempty D] (original : Fang.Interpretation D) :
    ∃ extended : Fang.Interpretation D,
      Fang.QuantifiedFOF.Skolem.PreservesBelow signature.functions.val.length
        (Fang.EqualityBridge.reserveInterpretation reservation.equality.val original) extended ∧
      (Fang.Equality.models (Fang.EqualityBridge.recoverInterpretation original extended) equality ↔
        retained.Models (Fang.EqualityBridge.reserveInterpretation reservation.equality.val original) ∧
        SignedDeclarationsHold
          (Fang.EqualityBridge.reserveInterpretation reservation.equality.val original) declarations.val) := by
  obtain ⟨extended, preserved, meaning⟩ := skolem_actual_problem_models success retained
    originalFunctions blocks steps
    (Fang.EqualityBridge.reserveInterpretation reservation.equality.val original)
  exact ⟨extended, preserved,
    (actualProblem_models original extended reservation signature.functions.val.length
      valid preserved converted).symm.trans meaning⟩

/-- An accepted ordered equality refutation excludes every reserved-equality
    model of the original retained CNF and signed quantified declarations.
    This is not yet an original-byte certificate endpoint. -/
theorem actual_preprocessing_check_unsat
    {declarations : Slice fang_skolem_core.Declaration}
    {signature : fang_skolem_core.fang_quantified_fof_core.Signature}
    {limits : fang_skolem_core.Limits} {output : fang_skolem_core.Skolemized}
    (success : fang_skolem_core.skolemize_problem declarations signature limits = .ok (.Ok output))
    (retained : Fang.Problem) (originalFunctions : ProblemBelow signature.functions.val.length retained)
    (blocks : List Fang.Problem)
    (steps : List.Forall₂ ActualClausificationStep output.formulas.val blocks)
    (reservation : Reservation) (valid : FangEqualityBridge.ValidReservation reservation)
    (equality : Fang.Equality.Problem)
    (converted : ActualProblemConversion reservation (retained ++ blocks.flatten) equality)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check equality certificate = .ok ()) :
    ¬ ∃ (D : Type) (_ : Nonempty D) (original : Fang.Interpretation D),
      retained.Models (Fang.EqualityBridge.reserveInterpretation reservation.equality.val original) ∧
      SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation reservation.equality.val original) declarations.val := by
  rintro ⟨D, nonempty, original, retainedModel, declarationModel⟩
  let : Nonempty D := nonempty
  obtain ⟨extended, _, meaning⟩ := actual_preprocessing_models success retained originalFunctions
    blocks steps reservation valid equality converted original
  exact Fang.Equality.Ordered.check_unsat equality certificate accepted
    ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation original extended,
      meaning.mpr ⟨retainedModel, declarationModel⟩⟩

end FangQuantifiedEquality
