/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Version-8 acceptance over a sealed bundle: the bundle's numeric input runs
   through the accepted transport, extracted preprocessing and conversion chain
   of `ExpandedReplay.prepare`, then the accepted envelope `checkProblem`. -/
import ExpandedCertificate
import BundleNumeric

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8

open Aeneas.Std
open Fang.QuantifiedCertificate FangQuantifiedPipeline
open FangQuantifiedEqualityReplay (bind_success mapError_success)
open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage.FramerV2

/-- The steps of `ExpandedReplay.prepare` after decoding, for any numeric input. -/
def replayFrom (numeric : NumericInput) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except ReplayError ReplayPrepared := do
  let encoded ← (transport numeric maximumPredicates).mapError .transport
  let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing
  let blocks ← (FangOriginalReplay.replayBlocks limits transformed.formulas.val).mapError .preprocessing
  let ordinary ← (FangOriginalReplay.assemble numeric.declarations blocks).mapError .preprocessing
  let equality ← (FangQuantifiedEqualityReplay.Conversion.problem encoded.reservation maximumLiterals
    ordinary).mapError .conversion
  pure ⟨numeric, equality, transformed.signature.functions.val.map (fun value => value.val),
    numeric.predicates.map Prod.snd⟩

/-- The accepted `prepare` is decoding followed by `replayFrom`. -/
theorem prepare_eq (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    prepare bytes maximumBytes limits maximumPredicates maximumLiterals =
      (decodeNumeric bytes maximumBytes >>= fun numeric =>
        replayFrom numeric limits maximumPredicates maximumLiterals) := rfl

theorem replayFrom_witness {numeric limits maximumPredicates maximumLiterals prepared}
    (success : replayFrom numeric limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ encoded transformed blocks ordinary,
      prepared.original = numeric ∧
      transport numeric maximumPredicates = .ok encoded ∧
      fang_skolem_core.skolemize_problem encoded.declarations encoded.signature limits.skolem = .ok (.Ok transformed) ∧
      List.Forall₂ ActualClausificationStep transformed.formulas.val blocks ∧
      MixedLayout numeric.declarations blocks ordinary ∧
      FangQuantifiedEquality.ActualProblemConversion encoded.reservation ordinary prepared.problem := by
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨blocks, blocksRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  obtain ⟨equality, conversionRun, success⟩ := bind_success success
  cases Except.ok.inj success
  exact ⟨encoded, transformed, blocks, ordinary, rfl, mapError_success inputRun,
    FangOriginalReplay.observe_success (mapError_success skolemRun),
    FangOriginalReplay.replayBlocks_steps (mapError_success blocksRun),
    FangOriginalReplay.assemble_layout (mapError_success assemblyRun),
    FangQuantifiedEqualityReplay.Conversion.problem_actual (mapError_success conversionRun)⟩

/-- The argument of `prepare_check_original_unsat`, for any numeric input whose
    function IDs are table IDs. -/
theorem replayFrom_check_unsat {numeric limits maximumPredicates maximumLiterals prepared}
    (below : ∀ value ∈ numeric.declarations, DeclarationBelow numeric.functions.length value)
    (success : replayFrom numeric limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ numeric.Satisfiable := by
  obtain ⟨encoded, transformed, blocks, ordinary, _, inputRun, skolemRun, steps, layout, converted⟩ :=
    replayFrom_witness success
  rintro ⟨D, nonempty, original, holds⟩
  let : Nonempty D := nonempty
  obtain ⟨valid, _, slot, _, functions, _⟩ := transport_tables inputRun
  have count : encoded.signature.functions.val.length = numeric.functions.length := by
    simpa only [List.length_map] using congrArg List.length functions
  have bounded : ProblemBelow encoded.signature.functions.val.length (retained numeric.declarations) := by
    rw [count]
    exact retained_below below
  have originalHolds := transport_models inputRun holds
  have reservedHolds :
      (retained numeric.declarations).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original) ∧
      SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
        encoded.declarations.val := by
    rw [slot, ← reserve_interpretation]
    exact originalHolds
  obtain ⟨extended, preserved, grouped⟩ := skolem_actual_problem_models skolemRun
    (retained numeric.declarations) bounded blocks steps
    (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
  have groupedModel := grouped.mpr reservedHolds
  have mixedModel : ordinary.Models extended := (mixedLayout_models layout extended).mpr
    ((FangQuantifiedPipeline.models_append extended _ _).mp groupedModel)
  have equalityModel := (FangQuantifiedEquality.actualProblem_models original extended
    encoded.reservation encoded.signature.functions.val.length valid preserved converted).mp mixedModel
  exact Fang.Equality.Ordered.check_unsat prepared.problem certificate accepted
    ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation original extended, equalityModel⟩

inductive BundleReplayError where
  | bundle : BundleError → BundleReplayError
  | replay : ReplayError → BundleReplayError

def prepareBundle (files : List (Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleReplayError ReplayPrepared := do
  let numeric ← (bundleNumeric files maximumBytes).mapError .bundle
  (replayFrom numeric limits maximumPredicates maximumLiterals).mapError .replay

inductive BundleAcceptError where
  | replay : BundleReplayError → BundleAcceptError
  | certificate : CertificateError → BundleAcceptError

/-- Version-8 acceptance for a sealed bundle. Every file is given explicitly;
    the certificate envelope and checker are the accepted `checkProblem`. -/
def acceptsBundle (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleAcceptError Unit := do
  let prepared ← (prepareBundle files maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

/-- Acceptance excludes every model of the sealed bundle, distinct objects
    separated. The only premise is the successful `acceptsBundle` call. -/
theorem acceptsBundle_original_unsat {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ ByteBundleSatisfiable files maximumBytes bundleFuel := by
  obtain ⟨prepared, prepareRun, checked⟩ := bind_success accepted
  obtain ⟨numeric, numericRun, replayRun⟩ := bind_success (mapError_success prepareRun)
  obtain ⟨parsed, _, _, _, refuted⟩ := checkProblem_success (mapError_success checked)
  have numericOk := mapError_success numericRun
  exact bundleNumeric_unsat numericOk
    (replayFrom_check_unsat (bundleNumeric_below numericOk) (mapError_success replayRun) parsed refuted)

/-- `¬ ByteBundleSatisfiable` alone holds for any bundle that does not frame,
    is not well shaped or does not expand. Acceptance also establishes those
    three facts, so its refutation is about an actual expansion. -/
def BundleRefuted (files : List (Key × List UInt8)) (maximumBytes fuel : Nat) : Prop :=
  (∃ bundle items, frameBundle files maximumBytes = .ok bundle ∧ wellShaped bundle fuel = true ∧
    expand bundle fuel = .ok items) ∧ ¬ ByteBundleSatisfiable files maximumBytes fuel

theorem acceptsBundle_refuted {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    BundleRefuted files maximumBytes bundleFuel := by
  refine ⟨?_, acceptsBundle_original_unsat accepted⟩
  obtain ⟨prepared, prepareRun, _⟩ := bind_success accepted
  obtain ⟨numeric, numericRun, _⟩ := bind_success (mapError_success prepareRun)
  obtain ⟨bundle, items, _, framed, shaped, expanded, _, _⟩ := bundleNumeric_witness (mapError_success numericRun)
  exact ⟨bundle, items, framed, shaped, expanded⟩

/-- The same content with the model quantifier written out: the accepted files
    frame into a well-shaped bundle whose expansion has no model in which
    different distinct objects denote different elements. -/
theorem acceptsBundle_no_model {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ∃ bundle items, frameBundle files maximumBytes = .ok bundle ∧ wellShaped bundle bundleFuel = true ∧
      expand bundle bundleFuel = .ok items ∧
      ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
        Models (source (declarationsOf bundle items)) model →
        ¬ NamedSeparated model (objectNames (declarationsOf bundle items)) := by
  obtain ⟨⟨bundle, items, framed, shaped, expanded⟩, unsat⟩ := acceptsBundle_refuted accepted
  exact ⟨bundle, items, framed, shaped, expanded, fun D nonempty model models separated =>
    unsat ⟨bundle, items, framed, shaped, expanded, D, nonempty, model, models, separated⟩⟩

theorem reachWalk_formulas (bundle : Bundle) (recurse : List Nat → Nat → List Nat → Except Failure (List Nat))
    (stack : List Nat) (key : Key) (order : List Nat) :
    ∀ values : List Declaration, reachWalk bundle recurse stack key (values.map .formula) order = .ok order
  | [] => rfl
  | _ :: rest => reachWalk_formulas bundle recurse stack key order rest

theorem reach_single (key : Key) (values : List Declaration) (fuel : Nat) :
    reach [⟨key, values.map .formula⟩] (fuel + 1) [0] 0 [0] = .ok [0] := by
  simp only [reach, List.getElem?_cons_zero]
  exact reachWalk_formulas _ _ _ _ _ values

theorem single_shaped (key : Key) (values : List Declaration) (wellFormed : keyWellFormed key = true) :
    wellShaped [⟨key, values.map .formula⟩] bundleFuel = true := by
  have reached : reach [⟨key, values.map .formula⟩] 17 [0] 0 [0] = .ok [0] := reach_single key values 16
  simp [wellShaped, bundleFuel, reached, wellFormed]

/-- One file that both the accepted decoder and the framer read the same way,
    without distinct objects, gives exactly the accepted version-8 replay. -/
theorem prepareBundle_single {bytes : List UInt8} {maximumBytes : Nat} {values : List Declaration}
    {input : NumericInput} {key : Key} (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize)
    (decoded : CnfBoolean.decodeBytes bytes maximumBytes = .ok values)
    (encoded : readInput values = some input)
    (framed : frameFile bytes maximumBytes = .ok (values.map .formula))
    (noObjects : objectNames values = [])
    (wellFormed : keyWellFormed key = true) :
    prepareBundle [(key, bytes)] maximumBytes limits maximumPredicates maximumLiterals =
      (prepare bytes maximumBytes limits maximumPredicates maximumLiterals).mapError .replay := by
  have bundled : frameBundle [(key, bytes)] maximumBytes = .ok [⟨key, values.map .formula⟩] := by
    simp [frameBundle, framed]
  have expanded := expand_single key values 16
  have numeric : bundleNumeric [(key, bytes)] maximumBytes = .ok input := by
    have empty : distinctAxioms input.predicates.length (objectIds input values) = [] := by
      simp [objectIds, noObjects, distinctAxioms, pairs]
    simp only [bundleNumeric, bundled, single_shaped key values wellFormed, ↓reduceIte]
    rw [show bundleFuel = 16 + 1 from rfl, expanded]
    simp only [declarationsOf_single, encoded]
    rw [empty]
    rfl
  have decodedNumeric : decodeNumeric bytes maximumBytes = .ok input := by
    unfold decodeNumeric
    rw [decoded]
    simp only [Except.mapError, Bind.bind, Except.bind, encoded]
  rw [prepare_eq, decodedNumeric]
  simp only [prepareBundle, numeric, Except.mapError, Bind.bind, Except.bind]

def liftError : AcceptError → BundleAcceptError
  | .replay error => .replay (.replay error)
  | .certificate error => .certificate error

/-- The single-file reduction to the accepted version-8 `accepts`. -/
theorem acceptsBundle_single {bytes : List UInt8} {maximumBytes : Nat} {values : List Declaration}
    {input : NumericInput} {key : Key} (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize)
    (decoded : CnfBoolean.decodeBytes bytes maximumBytes = .ok values)
    (encoded : readInput values = some input)
    (framed : frameFile bytes maximumBytes = .ok (values.map .formula))
    (noObjects : objectNames values = [])
    (wellFormed : keyWellFormed key = true) :
    acceptsBundle [(key, bytes)] maximumBytes proof limits maximumPredicates maximumLiterals =
      (accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals).mapError liftError := by
  unfold acceptsBundle accepts
  rw [prepareBundle_single limits maximumPredicates maximumLiterals decoded encoded framed noObjects wellFormed]
  cases prepare bytes maximumBytes limits maximumPredicates maximumLiterals with
  | error error => rfl
  | ok prepared =>
    simp only [Except.mapError, Bind.bind, Except.bind]
    cases checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof <;> rfl

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.prepare_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.replayFrom_witness
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.replayFrom_check_unsat
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.acceptsBundle_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.acceptsBundle_refuted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.acceptsBundle_no_model
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.reachWalk_formulas
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.reach_single
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.single_shaped
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.prepareBundle_single
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.acceptsBundle_single

end Fang.TptpCandidate.FullFof.Coverage.BundleV8
