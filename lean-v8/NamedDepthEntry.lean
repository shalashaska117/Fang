/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The expanded entry with naming and the formula height as a parameter: the
   input is decoded as `acceptsLimitedD` decodes it, then the replay with
   naming runs on the numeric input. Acceptance proves that the original
   bytes have no model, for every declaration limit, height and threshold; at
   height 64 the entry is `acceptsNamed`. -/
import NamedCore
import ExpandedLimitDecoderDepth

namespace Fang.TptpCandidate.FullFof.Integration.Named
open Aeneas Aeneas.Std
open Fang.TptpCandidate.FullFof.Integration
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-- Decoding at height `maxDepth`, then the replay with naming. -/
def prepareNamedD (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except NamedError ReplayPrepared := do
  let numeric ← (decodeNumericLimitedD limit maxDepth bytes maximumBytes).mapError .replay
  replayNamedFrom numeric limits threshold maximumPredicates maximumLiterals

/-- Acceptance of the prepared problem excludes every original byte model, for every
    declaration limit, height and threshold. -/
theorem prepareNamedD_check_original_unsat {limit maxDepth bytes maximumBytes limits threshold maximumPredicates
    maximumLiterals prepared}
    (success : prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨numeric, decoded, replayRun⟩ := bind_success success
  obtain ⟨values, parsed, numericRun⟩ := decodeNumericLimitedD_witness (mapError_success decoded)
  exact decodeUpToD_readInput_unsat parsed numericRun
    (replayNamedFrom_check_unsat (readInput_below numericRun) replayRun certificate accepted)

/-- The native entry with naming and both bounds as parameters; the envelope and checker of `acceptsNamed`. -/
def acceptsNamedD (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except AcceptNamedError Unit := do
  let prepared ← (prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates
    maximumLiterals).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

/-- Acceptance proves that the original bytes have no model, for every declaration limit, height and threshold. -/
theorem acceptsNamedD_original_unsat {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates
    maximumLiterals}
    (accepted : acceptsNamedD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨prepared, replayRun, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := checkProblem_success (mapError_success checked)
  exact prepareNamedD_check_original_unsat (mapError_success replayRun) parsed refuted

/-- On acceptance every atom of the checked problem has the arity its table lists. -/
theorem acceptsNamedD_signature {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates
    maximumLiterals}
    (accepted : acceptsNamedD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ∃ prepared, prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates
        maximumLiterals = .ok prepared ∧
      prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed prepared.functionArities
        prepared.predicateArities) = true := by
  obtain ⟨prepared, replayRun, checked⟩ := bind_success accepted
  obtain ⟨_, _, wellFormed, _, _⟩ := checkProblem_success (mapError_success checked)
  exact ⟨prepared, mapError_success replayRun, wellFormed⟩

/-- At height 64 the entry is `acceptsNamed`. -/
theorem acceptsNamedD_accepted (limit : Nat) : acceptsNamedD limit 64 = acceptsNamed limit := by
  have decoded : decodeNumericLimitedD limit 64 = decodeNumericLimited limit := by
    funext bytes maximumBytes
    unfold decodeNumericLimitedD decodeNumericLimited
    rw [decodeBytesLimitedD_eq, decodeBytesLimited_eq, decodeBytesUpToD_accepted]
    rfl
  funext bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals
  unfold acceptsNamedD prepareNamedD
  rw [decoded, ← prepareNamed_eq]
  rfl

end Fang.TptpCandidate.FullFof.Integration.Named
