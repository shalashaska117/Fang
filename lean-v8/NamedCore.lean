/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The replay with naming after decoding, for any numeric input, and the part of
   its soundness argument that every entry shares: once the Skolemized formulas
   and the retained clauses hold in a model that agrees with the reserved
   interpretation on every predicate, an accepted certificate is impossible.
   The bundle and signed entries restate their endpoints over these two results
   as the expanded entry does over `prepareNamed`. -/
import NamedReplay

namespace Fang.TptpCandidate.FullFof.Integration.Named
open Aeneas Aeneas.Std
open Fang.QuantifiedCertificate FangQuantifiedPipeline FangNaming
open Fang.TptpCandidate.FullFof.Integration
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-- The checks and conversion of `finishNamed`, over any retained declarations. -/
def finishWith (declarations : List NumericDeclaration) (original : fang_fof_equality_bridge.Reservation)
    (first : U32) (named : List Fang.Problem × U32 × List Usize) (ordinary : Fang.Problem)
    (maximumPredicates maximumLiterals : Usize) : Except NamedError Fang.Equality.Problem :=
  if problemBelow first.val (retained declarations) && problemBelow named.2.1.val ordinary &&
      named.2.2.length == named.2.1.val - first.val then do
    let table ← tableOf (original.original_predicates.val ++ named.2.2)
    let reservation ← observeReservation (fang_fof_equality_bridge.Reservation.new table maximumPredicates)
    ((FangQuantifiedEqualityReplay.Conversion.problem reservation maximumLiterals
      (renumberProblem original.equality.val (named.2.1.val - first.val) ordinary)).mapError .conversion).mapError
      .replay
  else .error .range

theorem finishNamed_success {numeric original functions first named ordinary maximumPredicates maximumLiterals
    prepared}
    (success : finishNamed numeric original functions first named ordinary maximumPredicates maximumLiterals =
      .ok prepared) :
    finishWith numeric.declarations original first named ordinary maximumPredicates maximumLiterals =
      .ok prepared.problem := by
  unfold finishNamed at success
  unfold finishWith
  split at success
  next checks =>
    rw [ite_eq_left checks]
    obtain ⟨table, tableRun, success⟩ := bind_success success
    obtain ⟨reservation, reservationRun, success⟩ := bind_success success
    obtain ⟨equality, conversionRun, success⟩ := bind_success success
    cases Except.ok.inj success
    simp only [tableRun, Bind.bind, Except.bind, reservationRun]
    exact conversionRun
  next => cases success

/-- From the named blocks on: the shared tail of every entry with naming. Given
    a model in which the retained clauses and the Skolemized formulas hold and
    whose predicates are those of the reserved interpretation, the prepared
    problem has a model, so no certificate is accepted. -/
theorem named_unsat {declarations : List NumericDeclaration} {original : fang_fof_equality_bridge.Reservation}
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
    (retainedModels : (retained declarations).Models skolemized)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check problem certificate = .ok ()) : False := by
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
    exact Fang.Equality.Ordered.check_unsat _ certificate accepted
      ⟨D, inferInstance, Fang.EqualityBridge.recoverInterpretation _ _, equalityModel⟩
  next => cases finished

/-- The steps of `prepareNamed` after decoding, for any numeric input. -/
def replayNamedFrom (numeric : NumericInput) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Usize) : Except NamedError ReplayPrepared := do
  let encoded ← ((transport numeric maximumPredicates).mapError .transport).mapError .replay
  let transformed ← ((FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing).mapError .replay
  let first ← firstNamed encoded.reservation.equality
  let named ← ((replayNamedBlocks limits threshold first.val first transformed.formulas.val).mapError
    .preprocessing).mapError .replay
  let ordinary ← ((FangOriginalReplay.assemble numeric.declarations named.1).mapError .preprocessing).mapError .replay
  finishNamed numeric encoded.reservation (transformed.signature.functions.val.map (fun value => value.val)) first
    named ordinary maximumPredicates maximumLiterals

/-- `prepareNamed` is decoding followed by `replayNamedFrom`. -/
theorem prepareNamed_eq (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Usize) :
    prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      ((decodeNumericLimited limit bytes maximumBytes).mapError .replay >>= fun numeric =>
        replayNamedFrom numeric limits threshold maximumPredicates maximumLiterals) := rfl

/-- The argument of `replayFrom_check_unsat` with naming: for any numeric input
    whose function IDs are table IDs, acceptance excludes every model. -/
theorem replayNamedFrom_check_unsat {numeric limits threshold maximumPredicates maximumLiterals prepared}
    (below : ∀ value ∈ numeric.declarations, DeclarationBelow numeric.functions.length value)
    (success : replayNamedFrom numeric limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ numeric.Satisfiable := by
  unfold replayNamedFrom at success
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨first, firstRun, success⟩ := bind_success success
  obtain ⟨named, namedRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  rintro ⟨D, nonempty, original, holds⟩
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
  exact named_unsat valid firstRun (mapError_twice namedRun) (mapError_twice assemblyRun)
    (finishNamed_success success) original
    skolemized preserved
    (fun formula member =>
      ⟨⟨_, skolemize_problem_scoped skolemSuccess formula member⟩,
        (FangSkolemCore.skolemize_problem_output skolemSuccess formula member).1,
        fun valuation => (meaning valuation).mp
          (fun declaration present => reservedHolds.2 declaration present valuation) formula member⟩)
    ((problem_preserved preserved _ bounded).mpr reservedHolds.1) certificate accepted

end Fang.TptpCandidate.FullFof.Integration.Named
