/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Reuse the actual preprocessing calls; construct all ordered conversion witnesses. -/
import EqualityClauseReplay
import ReservedByteEntry
import OriginalReplay

open Aeneas Aeneas.Std

namespace FangQuantifiedEqualityReplay

inductive Error where
  | input : FangQuantifiedEqualityInput.Error → Error
  | preprocessing : FangOriginalReplay.Error → Error
  | conversion : Conversion.Error → Error

structure Prepared where
  problem : Fang.Equality.Problem
  functionArities : List Nat
  predicateArities : List Nat

/-- The inherited removal/clausifier credits apply per FOF block. The bridge
    limit applies per output clause. Whole native execution needs its own process
    guard; this does not equate those limits with the Rust wrapper's cumulative credits. -/
def prepare (input : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except Error Prepared := do
  let encoded ← (FangQuantifiedEqualityInput.prepareInput input maximumPredicates).mapError .input
  let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing
  let blocks ← (FangOriginalReplay.replayBlocks limits transformed.formulas.val).mapError .preprocessing
  let ordinary ← (FangOriginalReplay.assemble
    (FangQuantifiedEqualityInput.numericDeclarations encoded.original.declarations) blocks).mapError .preprocessing
  let equality ← (Conversion.problem encoded.reservation maximumLiterals ordinary).mapError .conversion
  pure ⟨equality, transformed.signature.functions.val.map (fun value => value.val),
    encoded.original.originalPredicates.map Prod.snd⟩

theorem prepare_witness {input limits maximumPredicates maximumLiterals prepared}
    (success : prepare input limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ encoded transformed blocks ordinary,
      FangQuantifiedEqualityInput.prepareInput input maximumPredicates = .ok encoded ∧
      fang_skolem_core.skolemize_problem encoded.declarations encoded.signature limits.skolem = .ok (.Ok transformed) ∧
      List.Forall₂ FangQuantifiedPipeline.ActualClausificationStep transformed.formulas.val blocks ∧
      Fang.QuantifiedCertificate.MixedLayout
        (FangQuantifiedEqualityInput.numericDeclarations encoded.original.declarations) blocks ordinary ∧
      FangQuantifiedEquality.ActualProblemConversion encoded.reservation ordinary prepared.problem ∧
      prepared.functionArities = transformed.signature.functions.val.map (fun value => value.val) ∧
      prepared.predicateArities = encoded.original.originalPredicates.map Prod.snd := by
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨blocks, blocksRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  obtain ⟨equality, conversionRun, success⟩ := bind_success success
  cases Except.ok.inj success
  exact ⟨encoded, transformed, blocks, ordinary, mapError_success inputRun,
    FangOriginalReplay.observe_success (mapError_success skolemRun),
    FangOriginalReplay.replayBlocks_steps (mapError_success blocksRun),
    FangOriginalReplay.assemble_layout (mapError_success assemblyRun),
    Conversion.problem_actual (mapError_success conversionRun), rfl, rfl⟩

/-- Successful actual replay and the ordered equality checker suffice. There are
    no caller-supplied preprocessing, table, layout or conversion witnesses here.
    This accepts an AST certificate; a byte envelope and command are separate. -/
theorem prepare_check_original_unsat {input limits maximumPredicates maximumLiterals prepared}
    (success : prepare input limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ Fang.NamedQuantifiedEquality.Grammar.BytesSatisfiable (Fang.Source.Grammar.spelling input) := by
  obtain ⟨encoded, transformed, blocks, ordinary, inputRun, skolemRun, steps, layout, converted, _, _⟩ :=
    prepare_witness success
  exact FangQuantifiedEqualityInput.prepareInput_check_original_unsat
    inputRun skolemRun steps layout converted certificate accepted

end FangQuantifiedEqualityReplay
