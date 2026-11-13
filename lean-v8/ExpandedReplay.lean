/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Original expanded bytes through existing extracted preprocessing calls. -/
import ExpandedTransport
import EqualityOriginalReplay

namespace Fang.TptpCandidate.FullFof.Integration
open Aeneas.Std
open Fang.QuantifiedCertificate FangQuantifiedPipeline
open FangQuantifiedEqualityReplay (bind_success mapError_success)

inductive ReplayError where
  | input : Fang.TptpCandidate.Error → ReplayError
  | nonliteral
  | transport : FangQuantifiedEqualityInput.Error → ReplayError
  | preprocessing : FangOriginalReplay.Error → ReplayError
  | conversion : FangQuantifiedEqualityReplay.Conversion.Error → ReplayError

def decodeNumeric (bytes : List UInt8) (maximumBytes : Nat) : Except ReplayError NumericInput := do
  let source ← (CnfBoolean.decodeBytes bytes maximumBytes).mapError .input
  match readInput source with
  | none => .error .nonliteral
  | some input => .ok input

theorem decodeNumeric_witness {bytes maximum input}
    (success : decodeNumeric bytes maximum = .ok input) :
    ∃ values, CnfBoolean.decodeBytes bytes maximum = .ok values ∧ readInput values = some input := by
  obtain ⟨values, decoded, success⟩ := bind_success success
  cases encoded : readInput values with
  | none => simp [encoded] at success
  | some result =>
    have same : result = input := Except.ok.inj (by simpa only [encoded] using success)
    subst input
    exact ⟨values, mapError_success decoded, encoded⟩

structure ReplayPrepared where
  original : NumericInput
  problem : Fang.Equality.Problem
  functionArities : List Nat
  predicateArities : List Nat

/-- Stage credits retain the inherited checker policy: removal/clausification
    per FOF block and equality conversion per clause. Complete execution still
    needs an external process guard. No Rust resource-equivalence claim. -/
def prepare (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except ReplayError ReplayPrepared := do
  let numeric ← decodeNumeric bytes maximumBytes
  let encoded ← (transport numeric maximumPredicates).mapError .transport
  let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing
  let blocks ← (FangOriginalReplay.replayBlocks limits transformed.formulas.val).mapError .preprocessing
  let ordinary ← (FangOriginalReplay.assemble numeric.declarations blocks).mapError .preprocessing
  let equality ← (FangQuantifiedEqualityReplay.Conversion.problem encoded.reservation maximumLiterals
    ordinary).mapError .conversion
  pure ⟨numeric, equality, transformed.signature.functions.val.map (fun value => value.val),
    numeric.predicates.map Prod.snd⟩

theorem prepare_witness {bytes maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepare bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ values encoded transformed blocks ordinary,
      CnfBoolean.decodeBytes bytes maximumBytes = .ok values ∧
      readInput values = some prepared.original ∧
      transport prepared.original maximumPredicates = .ok encoded ∧
      fang_skolem_core.skolemize_problem encoded.declarations encoded.signature limits.skolem = .ok (.Ok transformed) ∧
      List.Forall₂ ActualClausificationStep transformed.formulas.val blocks ∧
      MixedLayout prepared.original.declarations blocks ordinary ∧
      FangQuantifiedEquality.ActualProblemConversion encoded.reservation ordinary prepared.problem ∧
      prepared.functionArities = transformed.signature.functions.val.map (fun value => value.val) ∧
      prepared.predicateArities = prepared.original.predicates.map Prod.snd := by
  obtain ⟨numeric, decoded, success⟩ := bind_success success
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨blocks, blocksRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  obtain ⟨equality, conversionRun, success⟩ := bind_success success
  cases Except.ok.inj success
  obtain ⟨values, parsed, numericRun⟩ := decodeNumeric_witness decoded
  exact ⟨values, encoded, transformed, blocks, ordinary, parsed, numericRun,
    mapError_success inputRun, FangOriginalReplay.observe_success (mapError_success skolemRun),
    FangOriginalReplay.replayBlocks_steps (mapError_success blocksRun),
    FangOriginalReplay.assemble_layout (mapError_success assemblyRun),
    FangQuantifiedEqualityReplay.Conversion.problem_actual (mapError_success conversionRun), rfl, rfl⟩

/-- The frontend's reserved-slot model and the bridge's reserved interpretation
    are the same definition with different names. -/
theorem reserve_interpretation {D : Type} (reserved : Nat) (model : Fang.Interpretation D) :
    Fang.TptpCandidate.FullFof.reserve reserved model =
      Fang.EqualityBridge.reserveInterpretation reserved model := rfl

/-- Actual replay and ordered AST-certificate acceptance exclude every original
    byte model. All table, preprocessing, layout and conversion witnesses come
    from the successful call. A v8 byte envelope and executable entry are separate. -/
theorem prepare_check_original_unsat {bytes maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepare bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨values, encoded, transformed, blocks, ordinary, decoded, numericRun,
    inputRun, skolemRun, steps, layout, converted, _, _⟩ := prepare_witness success
  apply decode_readInput_unsat decoded numericRun
  rintro ⟨D, nonempty, original, holds⟩
  let : Nonempty D := nonempty
  obtain ⟨valid, _, slot, _, _, _⟩ := transport_tables inputRun
  have originalHolds := transport_models inputRun holds
  have reservedHolds :
      (retained prepared.original.declarations).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original) ∧
      SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
        encoded.declarations.val := by
    rw [slot, ← reserve_interpretation]
    exact originalHolds
  obtain ⟨extended, preserved, grouped⟩ := skolem_actual_problem_models skolemRun
    (retained prepared.original.declarations) (transport_retained_below numericRun inputRun)
    blocks steps (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
  have groupedModel := grouped.mpr reservedHolds
  have mixedModel : ordinary.Models extended := (mixedLayout_models layout extended).mpr
    ((FangQuantifiedPipeline.models_append extended _ _).mp groupedModel)
  have equalityModel := (FangQuantifiedEquality.actualProblem_models original extended
    encoded.reservation encoded.signature.functions.val.length valid preserved converted).mp mixedModel
  exact Fang.Equality.Ordered.check_unsat prepared.problem certificate accepted
    ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation original extended, equalityModel⟩

#print axioms Fang.TptpCandidate.FullFof.Integration.decodeNumeric_witness
#print axioms Fang.TptpCandidate.FullFof.Integration.prepare_witness
#print axioms Fang.TptpCandidate.FullFof.Integration.reserve_interpretation
#print axioms Fang.TptpCandidate.FullFof.Integration.prepare_check_original_unsat

end Fang.TptpCandidate.FullFof.Integration
