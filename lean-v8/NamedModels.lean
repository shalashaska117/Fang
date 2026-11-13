/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Model extension through naming for the SAP document proofs. -/
import NamedCore

namespace Fang.TptpCandidate.FullFof.Integration.Named
open Aeneas Aeneas.Std
open Fang.QuantifiedCertificate FangQuantifiedPipeline FangNaming
open Fang.TptpCandidate.FullFof.Integration
open FangQuantifiedEqualityReplay (bind_success mapError_success)

theorem named_models {declarations : List NumericDeclaration} {original : fang_fof_equality_bridge.Reservation}
    {first : U32} {named : List Fang.Problem × U32 × List Usize} {ordinary : Fang.Problem}
    {limits : FangOriginalReplay.Limits} {threshold maximumPredicates maximumLiterals : Usize}
    {formulas : List fang_skolem_core.fang_quantified_fof_core.Nnf} {problem : Fang.Equality.Problem}
    (valid : original.equality.val = original.original_predicates.val.length)
    (firstRun : firstNamed original.equality = .ok first)
    (namedRun : replayNamedBlocks limits threshold first.val first formulas = .ok named)
    (assemblyRun : FangOriginalReplay.assemble declarations named.1 = .ok ordinary)
    (finished : finishWith declarations original first named ordinary maximumPredicates maximumLiterals =
      .ok problem)
    {D : Type} [Nonempty D] (base skolemized : Fang.Interpretation D) {bound : Nat}
    (preserved : Fang.QuantifiedFOF.Skolem.PreservesBelow bound
      (Fang.EqualityBridge.reserveInterpretation original.equality.val base) skolemized)
    (formulasHold : ∀ formula ∈ formulas,
      (∃ signature count, InputScoped signature (.Bound count) (skolemNnf formula)) ∧
        Fang.QuantifiedFOF.BinderRemoval.RectifiedWithin [] (FangSkolemCore.decodeIndependentNnf formula) ∧
        ∀ valuation, (FangSkolemCore.decodeIndependentNnf formula).Holds skolemized valuation)
    (retainedModels : (retained declarations).Models skolemized) :
    ∃ model : Fang.Interpretation D, Fang.Equality.models model problem := by
  unfold finishWith at finished
  split at finished
  next checks =>
    obtain ⟨table, tableRun, finished⟩ := bind_success finished
    obtain ⟨reservation, reservationRun, conversionRun⟩ := bind_success finished
    simp only [Bool.and_eq_true, beq_iff_eq] at checks
    obtain ⟨⟨retainedCheck, ordinaryCheck⟩, countCheck⟩ := checks
    have firstValue := firstNamed_success firstRun
    obtain ⟨extended, agree, blocksModels, _, _⟩ :=
      replayNamedBlocks_models limits threshold first.val skolemized formulas first named namedRun (le_refl _)
        formulasHold skolemized (agreeBelow_refl _ skolemized)
    have retainedExtended : (retained declarations).Models extended :=
      problem_agreeBelow agree (problemBelow_sound retainedCheck) retainedModels
    have layout := FangOriginalReplay.assemble_layout assemblyRun
    have ordinaryModels : ordinary.Models extended :=
      (mixedLayout_models layout extended).mpr ⟨retainedExtended, blocksModels⟩
    have renumbered := renumber_models original.equality.val (named.2.1.val - first.val) ordinary
      (fun clause member literal inside => by
        have := problemBelow_sound ordinaryCheck clause member literal inside
        omega)
      extended ordinaryModels
    obtain ⟨tableSame, reservationValid, _⟩ :=
      spec_eq_ok (FangEqualityBridge.reservation_new_spec table maximumPredicates)
        (observeReservation_success reservationRun)
    have equalityIndex : reservation.equality.val = original.equality.val + (named.2.1.val - first.val) := by
      have lengths := reservationValid
      unfold FangEqualityBridge.ValidReservation at lengths
      rw [lengths, tableSame, tableOf_success tableRun, List.length_append, countCheck, ← valid]
    have preserved' : Fang.QuantifiedFOF.Skolem.PreservesBelow 0
        (Fang.EqualityBridge.reserveInterpretation reservation.equality.val
          (renumberedModel original.equality.val (named.2.1.val - first.val) extended))
        (renumberedModel original.equality.val (named.2.1.val - first.val) extended) := by
      refine ⟨fun symbol below => absurd below (Nat.not_lt_zero _), fun predicate arguments => ?_⟩
      simp only [Fang.EqualityBridge.reserveInterpretation]
      split
      · rename_i atSlot
        rw [atSlot, equalityIndex]
        have back : previous original.equality.val (named.2.1.val - first.val)
            (original.equality.val + (named.2.1.val - first.val)) = original.equality.val := by
          unfold previous
          split_ifs <;> omega
        simp only [renumberedModel, back]
        rw [← agree.2 _ (by omega), preserved.2]
        simp [Fang.EqualityBridge.reserveInterpretation]
      · rfl
    have converted := FangQuantifiedEqualityReplay.Conversion.problem_actual (mapError_twice conversionRun)
    have equalityModel := (FangQuantifiedEquality.actualProblem_models _ _ reservation 0 reservationValid
      preserved' converted).mp renumbered
    exact ⟨Fang.EqualityBridge.recoverInterpretation _ _, equalityModel⟩
  next => cases finished

theorem replayNamedFrom_models {numeric limits threshold maximumPredicates maximumLiterals prepared}
    (below : ∀ value ∈ numeric.declarations, DeclarationBelow numeric.functions.length value)
    (success : replayNamedFrom numeric limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (satisfiable : numeric.Satisfiable) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  unfold replayNamedFrom at success
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨first, firstRun, success⟩ := bind_success success
  obtain ⟨named, namedRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  obtain ⟨D, nonempty, original, holds⟩ := satisfiable
  let : Nonempty D := nonempty
  have inputSuccess := mapError_twice inputRun
  obtain ⟨valid, _, slot, _, functions, _⟩ := transport_tables inputSuccess
  have count : encoded.signature.functions.val.length = numeric.functions.length := by
    simpa only [List.length_map] using congrArg List.length functions
  have bounded : ProblemBelow encoded.signature.functions.val.length (retained numeric.declarations) := by
    rw [count]
    exact retained_below below
  have reservedHolds :
      (retained numeric.declarations).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original) ∧
      SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
        encoded.declarations.val := by
    rw [slot, ← reserve_interpretation]
    exact transport_models inputSuccess holds
  have skolemSuccess := FangOriginalReplay.observe_success (mapError_twice skolemRun)
  obtain ⟨skolemized, preserved, meaning⟩ := FangSkolemCore.skolemize_problem_independent_meaning
    skolemSuccess (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
  obtain ⟨model, models⟩ := named_models valid firstRun (mapError_twice namedRun) (mapError_twice assemblyRun)
    (finishNamed_success success) original
    skolemized preserved
    (fun formula member =>
      ⟨⟨_, skolemize_problem_scoped skolemSuccess formula member⟩,
        (FangSkolemCore.skolemize_problem_output skolemSuccess formula member).1,
        fun valuation => (meaning valuation).mp
          (fun declaration present => reservedHolds.2 declaration present valuation) formula member⟩)
    ((problem_preserved preserved _ bounded).mpr reservedHolds.1)
  exact ⟨D, nonempty, model, models⟩

theorem prepareNamed_models {limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (satisfiable : CnfBoolean.BytesSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  rw [prepareNamed_eq] at success
  obtain ⟨numeric, decoded, replay⟩ := bind_success success
  obtain ⟨values, parsed, numericRun⟩ := decodeNumericLimited_witness (mapError_success decoded)
  exact replayNamedFrom_models (readInput_below numericRun) replay
    (((decodeUpTo_bytes_satisfiable parsed).trans
      (readInput_satisfiable numericRun (decodeUpTo_closed parsed))).mp satisfiable)

theorem prepareNamed_original {limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals = .ok prepared) :
    ∃ values, decodeBytesUpTo limit bytes maximumBytes = .ok values ∧
      readInput values = some prepared.original := by
  unfold prepareNamed at success
  obtain ⟨numeric, decoded, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  unfold finishNamed at success
  split at success
  next =>
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    cases Except.ok.inj success
    exact decodeNumericLimited_witness (mapError_success decoded)
  next => cases success

end Fang.TptpCandidate.FullFof.Integration.Named
