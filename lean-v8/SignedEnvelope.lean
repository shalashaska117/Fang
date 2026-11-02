/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Version-8 acceptance of signed role tasks: signed prepare, then the accepted `checkProblem`. -/
import SignedReplay
import ExpandedEnvelope

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Signed
open FangQuantifiedEqualityReplay (bind_success mapError_success)

inductive SignedAcceptError where
  | replay : SignedError → SignedAcceptError
  | certificate : FullFof.Integration.CertificateError → SignedAcceptError

/-- The certificate for the original conjecture with this index among all conjectures, in source order. -/
def acceptsGoal (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except SignedAcceptError Unit := do
  let prepared ← (prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate

/-- The certificate for the satisfiability task of input without an original conjecture. -/
def acceptsInputs (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except SignedAcceptError Unit := do
  let prepared ← (prepareInputs bytes maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities
    prepared.predicateArities proof).mapError .certificate

theorem acceptsGoal_replay {bytes maximumBytes index proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      ∃ parsed, Fang.Equality.Ordered.check prepared.replay.problem parsed = .ok () := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact ⟨prepared, mapError_success run, parsed, refuted⟩

/-- Acceptance of one goal's certificate proves that the original premises entail that original conjecture, for the independent byte grammar. -/
theorem acceptsGoal_entails {bytes maximumBytes index proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      ∃ values, Bytes.ByteParsed bytes maximumBytes values ∧ Bytes.Closed values ∧
        prepared.goal ∈ Roles.goals (Bytes.source values) ∧
        ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
            Bytes.sentence model prepared.goal.original := by
  obtain ⟨prepared, run, parsed, refuted⟩ := acceptsGoal_replay accepted
  exact ⟨prepared, run, prepareGoal_check_entails run parsed refuted⟩

/-- Theorem endpoint over version-8 certificates: at least one original conjecture, and an accepted certificate for each one. -/
theorem acceptsGoals_theorem {bytes maximumBytes values limits maximumPredicates maximumLiterals}
    (decoded : Bytes.decodeBytes bytes maximumBytes = .ok values)
    (nonempty : Roles.goals (Bytes.source values) ≠ [])
    (accepted : ∀ goal ∈ Roles.goals (Bytes.source values), ∃ index prepared proof,
      prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      prepared.goal = goal ∧
      acceptsGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok ()) :
    BytesTheorem bytes maximumBytes := by
  apply prepareGoals_check_theorem decoded nonempty
  intro goal member
  obtain ⟨index, prepared, proof, run, same, checked⟩ := accepted goal member
  obtain ⟨other, otherRun, parsed, refuted⟩ := acceptsGoal_replay checked
  have equal : other = prepared := Except.ok.inj (otherRun.symm.trans run)
  subst equal
  exact ⟨index, other, parsed, run, same, refuted⟩

/-- Acceptance of the no-goal task's certificate proves that the accepted positive inputs are unsatisfiable. -/
theorem acceptsInputs_unsat {bytes maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsInputs bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximumBytes := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareInputs_check_unsat (mapError_success run) parsed refuted

#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoal_replay
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoal_entails
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoals_theorem
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsInputs_unsat

end Fang.TptpCandidate.Roles.Signed
