/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EqualityOriginalReplay
import EqualityOriginalCertificateInput

open Aeneas Aeneas.Std

namespace FangQuantifiedEqualityCertificate

inductive Error where
  | replay : FangQuantifiedEqualityReplay.Error → Error
  | prepared : PreparedError → Error

/-- Replay precedes certificate decoding. All execution needs an external guard;
    no SAT outcome or native/kernel capability is supplied by this definition. -/
def accepts (input proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except Error Unit := do
  let prepared ← (FangQuantifiedEqualityReplay.prepare input limits
    maximumPredicates maximumLiterals).mapError .replay
  (checkPrepared prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .prepared

theorem accepts_replay_success {input proof limits maximumPredicates maximumLiterals}
    (accepted : accepts input proof limits maximumPredicates maximumLiterals = .ok ()) :
    ∃ prepared, FangQuantifiedEqualityReplay.prepare input limits maximumPredicates maximumLiterals = .ok prepared ∧
      checkPrepared prepared.problem prepared.functionArities prepared.predicateArities proof = .ok () := by
  obtain ⟨prepared, replayRun, checked⟩ := FangQuantifiedEqualityReplay.bind_success accepted
  exact ⟨prepared, FangQuantifiedEqualityReplay.mapError_success replayRun,
    FangQuantifiedEqualityReplay.mapError_success checked⟩

theorem accepts_original_unsat {input proof limits maximumPredicates maximumLiterals}
    (accepted : accepts input proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ Fang.NamedQuantifiedEquality.Grammar.BytesSatisfiable (Fang.Source.Grammar.spelling input) := by
  obtain ⟨prepared, replayRun, checked⟩ := accepts_replay_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := checkPrepared_success checked
  exact FangQuantifiedEqualityReplay.prepare_check_original_unsat replayRun parsed refuted

theorem accepts_replay_error {input proof limits maximumPredicates maximumLiterals error}
    (rejected : FangQuantifiedEqualityReplay.prepare input limits maximumPredicates maximumLiterals = .error error) :
    accepts input proof limits maximumPredicates maximumLiterals = .error (.replay error) := by
  simp [accepts, rejected, Except.mapError, Bind.bind, Except.bind]

end FangQuantifiedEqualityCertificate
