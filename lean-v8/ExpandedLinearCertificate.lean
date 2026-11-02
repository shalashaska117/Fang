/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The version-8 checker with the linear lexer and the counted declaration
   decoder. Each definition is the accepted one with the decoder replaced, and is
   proved equal to it, so the accepted original-byte theorem transfers by
   rewriting. -/
import ExpandedFastCertificate
import ExpandedDecoder

namespace Fang.TptpCandidate.FullFof.Integration

def decodeNumericLinear (bytes : List UInt8) (maximumBytes : Nat) : Except ReplayError NumericInput := do
  let source ← (decodeBytesLinear bytes maximumBytes).mapError .input
  match readInput source with
  | none => .error .nonliteral
  | some input => .ok input

theorem decodeNumericLinear_eq (bytes : List UInt8) (maximumBytes : Nat) :
    decodeNumericLinear bytes maximumBytes = decodeNumeric bytes maximumBytes := by
  unfold decodeNumericLinear decodeNumeric
  rw [decodeBytesLinear_eq]
  -- The two definitions use distinct auxiliary match functions with equal bodies.
  rfl

def prepareLinear (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except ReplayError ReplayPrepared := do
  let numeric ← decodeNumericLinear bytes maximumBytes
  let encoded ← (transport numeric maximumPredicates).mapError .transport
  let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing
  let blocks ← (FangOriginalReplay.replayBlocks limits transformed.formulas.val).mapError .preprocessing
  let ordinary ← (FangOriginalReplay.assemble numeric.declarations blocks).mapError .preprocessing
  let equality ← (FangQuantifiedEqualityReplay.Conversion.problem encoded.reservation maximumLiterals
    ordinary).mapError .conversion
  pure ⟨numeric, equality, transformed.signature.functions.val.map (fun value => value.val),
    numeric.predicates.map Prod.snd⟩

theorem prepareLinear_eq (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    prepareLinear bytes maximumBytes limits maximumPredicates maximumLiterals =
      prepare bytes maximumBytes limits maximumPredicates maximumLiterals := by
  unfold prepareLinear prepare
  rw [decodeNumericLinear_eq]

/-- The native entry. Same envelope and checker as `accepts`; only the lexer and the decoder's length bookkeeping differ. -/
def acceptsLinear (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    Except AcceptError Unit := do
  let prepared ← (prepareLinear bytes maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

theorem acceptsLinear_eq (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    acceptsLinear bytes maximumBytes proof limits maximumPredicates maximumLiterals =
      accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals := by
  unfold acceptsLinear accepts
  rw [prepareLinear_eq]

/-- The accepted endpoint, transferred by rewriting. -/
theorem acceptsLinear_original_unsat {bytes maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsLinear bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  rw [acceptsLinear_eq] at accepted
  exact accepts_original_unsat accepted

#print axioms Fang.TptpCandidate.FullFof.Integration.decodeNumericLinear_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.prepareLinear_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.acceptsLinear_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.acceptsLinear_original_unsat

end Fang.TptpCandidate.FullFof.Integration
