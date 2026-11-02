/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   A separate version-7 envelope around the unchanged ordered equality node grammar. -/
import EqualityOrderedCertificateInput

namespace FangQuantifiedEqualityCertificate
open Fang Frontend

inductive PreparedError where
  | certificate : String → PreparedError
  | signature
  | inference : Equality.TraceError → PreparedError

def certificate (fuel : Nat) : Parser Equality.Ordered.Certificate := do
  expect "("
  expect "fang-proof"
  let version ← natural
  if version != 7 then fail "unsupported: quantified equality certificate version"
  expect "("
  expect "preprocessing"
  expect "nested-fof-equality-skolem-distributive-v1"
  expect ")"
  let (steps, finalId) ← EqualityOrderedCertificateInput.nodes fuel 0
  expect ")"
  if (← peek).isSome then fail "invalid-certificate: trailing tokens"
  pure { steps, final := finalId }

def decodeCertificate (input : String) : Except String Equality.Ordered.Certificate := do
  let tokens ← Frontend.tokenize input
  let (result, _) ← certificate (tokens.length + 1) { tokens, endOffset := input.utf8ByteSize }
  pure result

def decodes (input : String) : Bool :=
  match decodeCertificate input with
  | .ok _ => true
  | .error _ => false

/-- The signature gate checks the prepared clauses and every claimed clause and
    substitution image. The ordered checker supplies the logical decision. -/
def checkPrepared (problem : Equality.Problem) (functions predicates : List Nat)
    (proof : String) : Except PreparedError Unit := do
  let parsed ← (decodeCertificate proof).mapError .certificate
  if !(problem.all (EqualityCertificateInput.clauseWellFormed functions predicates)) ||
      !(EqualityOrderedCertificateInput.certificateWellFormed functions predicates parsed) then
    .error .signature
  else (Equality.Ordered.check problem parsed).mapError .inference

theorem checkPrepared_success {problem functions predicates proof}
    (accepted : checkPrepared problem functions predicates proof = .ok ()) :
    ∃ parsed, decodeCertificate proof = .ok parsed ∧
      problem.all (EqualityCertificateInput.clauseWellFormed functions predicates) = true ∧
      EqualityOrderedCertificateInput.certificateWellFormed functions predicates parsed = true ∧
      Equality.Ordered.check problem parsed = .ok () := by
  unfold checkPrepared at accepted
  cases parsedRun : decodeCertificate proof with
  | error error => simp [parsedRun, Except.mapError, bind, Except.bind] at accepted
  | ok parsed =>
    simp only [parsedRun, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
    · rename_i valid
      have both : problem.all (EqualityCertificateInput.clauseWellFormed functions predicates) = true ∧
          EqualityOrderedCertificateInput.certificateWellFormed functions predicates parsed = true := by
        simpa using valid
      refine ⟨parsed, rfl, both.1, both.2, ?_⟩
      cases checked : Equality.Ordered.check problem parsed with
      | error error => simp [checked] at accepted
      | ok value => cases value; rfl

theorem checkPrepared_certificate_error {problem functions predicates proof message}
    (rejected : decodeCertificate proof = .error message) :
    checkPrepared problem functions predicates proof = .error (.certificate message) := by
  simp [checkPrepared, rejected, Except.mapError, bind, Except.bind]

theorem checkPrepared_signature_error {problem functions predicates proof parsed}
    (decoded : decodeCertificate proof = .ok parsed)
    (invalid : problem.all (EqualityCertificateInput.clauseWellFormed functions predicates) = false ∨
      EqualityOrderedCertificateInput.certificateWellFormed functions predicates parsed = false) :
    checkPrepared problem functions predicates proof = .error .signature := by
  rcases invalid with invalid | invalid <;>
    simp [checkPrepared, decoded, invalid, Except.mapError, bind, Except.bind]

end FangQuantifiedEqualityCertificate
