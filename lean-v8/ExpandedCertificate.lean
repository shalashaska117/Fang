/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Version-8 acceptance: replay of the original bytes, then the envelope check. -/
import ExpandedReplay
import ExpandedEnvelope

namespace Fang.TptpCandidate.FullFof.Integration
open FangQuantifiedEqualityReplay (bind_success mapError_success)

inductive AcceptError where
  | replay : ReplayError → AcceptError
  | certificate : CertificateError → AcceptError

/-- Replay of the original bytes precedes certificate decoding. Every execution
    needs an external guard; there is no SAT outcome here. -/
def accepts (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    Except AcceptError Unit := do
  let prepared ← (prepare bytes maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

theorem accepts_replay_success {bytes maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ∃ prepared, prepare bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared ∧
      checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof = .ok () := by
  obtain ⟨prepared, replayRun, checked⟩ := bind_success accepted
  exact ⟨prepared, mapError_success replayRun, mapError_success checked⟩

/-- Acceptance of a version-8 certificate excludes every model of the original
    bytes. The only premise is the actual successful `accepts` call. -/
theorem accepts_original_unsat {bytes maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨prepared, replayRun, checked⟩ := accepts_replay_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := checkProblem_success checked
  exact prepare_check_original_unsat replayRun parsed refuted

theorem accepts_replay_error {bytes maximumBytes proof limits maximumPredicates maximumLiterals error}
    (rejected : prepare bytes maximumBytes limits maximumPredicates maximumLiterals = .error error) :
    accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals = .error (.replay error) := by
  simp [accepts, rejected, Except.mapError, Bind.bind, Except.bind]

#print axioms Fang.TptpCandidate.FullFof.Integration.accepts_replay_success
#print axioms Fang.TptpCandidate.FullFof.Integration.accepts_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.accepts_replay_error

end Fang.TptpCandidate.FullFof.Integration
