/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The version-8 checker with the linear lexer. Each definition is the accepted
   one with the lexer replaced, and is proved equal to it, so the accepted
   original-byte theorem transfers by rewriting. -/
import ExpandedCertificate
import ExpandedLexer

namespace Fang.TptpCandidate.FullFof.Integration

def decodeBytesFast (input : List UInt8) (maximumBytes : Nat) :=
  (fastTokenizeBytes input maximumBytes).bind fun tokens =>
    CnfBoolean.declarations (tokens.length + 1) [] input.length tokens

theorem decodeBytesFast_eq (input : List UInt8) (maximumBytes : Nat) :
    decodeBytesFast input maximumBytes = CnfBoolean.decodeBytes input maximumBytes := by
  unfold decodeBytesFast CnfBoolean.decodeBytes
  rw [fastTokenizeBytes_eq]
  rfl

def decodeNumericFast (bytes : List UInt8) (maximumBytes : Nat) : Except ReplayError NumericInput := do
  let source ← (decodeBytesFast bytes maximumBytes).mapError .input
  match readInput source with
  | none => .error .nonliteral
  | some input => .ok input

theorem decodeNumericFast_eq (bytes : List UInt8) (maximumBytes : Nat) :
    decodeNumericFast bytes maximumBytes = decodeNumeric bytes maximumBytes := by
  unfold decodeNumericFast decodeNumeric
  rw [decodeBytesFast_eq]
  -- The two definitions use distinct auxiliary match functions with equal bodies.
  rfl

def prepareFast (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except ReplayError ReplayPrepared := do
  let numeric ← decodeNumericFast bytes maximumBytes
  let encoded ← (transport numeric maximumPredicates).mapError .transport
  let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing
  let blocks ← (FangOriginalReplay.replayBlocks limits transformed.formulas.val).mapError .preprocessing
  let ordinary ← (FangOriginalReplay.assemble numeric.declarations blocks).mapError .preprocessing
  let equality ← (FangQuantifiedEqualityReplay.Conversion.problem encoded.reservation maximumLiterals
    ordinary).mapError .conversion
  pure ⟨numeric, equality, transformed.signature.functions.val.map (fun value => value.val),
    numeric.predicates.map Prod.snd⟩

theorem prepareFast_eq (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    prepareFast bytes maximumBytes limits maximumPredicates maximumLiterals =
      prepare bytes maximumBytes limits maximumPredicates maximumLiterals := by
  unfold prepareFast prepare
  rw [decodeNumericFast_eq]

/-- The native entry. Same envelope and checker as `accepts`; only the lexer differs. -/
def acceptsFast (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    Except AcceptError Unit := do
  let prepared ← (prepareFast bytes maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

theorem acceptsFast_eq (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    acceptsFast bytes maximumBytes proof limits maximumPredicates maximumLiterals =
      accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals := by
  unfold acceptsFast accepts
  rw [prepareFast_eq]

/-- The accepted endpoint, transferred by rewriting. -/
theorem acceptsFast_original_unsat {bytes maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsFast bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  rw [acceptsFast_eq] at accepted
  exact accepts_original_unsat accepted

#print axioms Fang.TptpCandidate.FullFof.Integration.decodeBytesFast_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.decodeNumericFast_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.prepareFast_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.acceptsFast_eq
#print axioms Fang.TptpCandidate.FullFof.Integration.acceptsFast_original_unsat

end Fang.TptpCandidate.FullFof.Integration
