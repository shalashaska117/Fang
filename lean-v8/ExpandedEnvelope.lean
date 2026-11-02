/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Version-8 envelope for expanded original input. Everything after the header
   is the unchanged ordered equality node grammar used by versions 5 and 7. -/
import EqualityOrderedCertificateInput

namespace Fang.TptpCandidate.FullFof.Integration

def v8Marker : String := "expanded-fof-equality-skolem-distributive-v1"

inductive CertificateError where
  | certificate : String → CertificateError
  | signature
  | inference : Fang.Equality.TraceError → CertificateError

def v8Certificate (fuel : Nat) : Fang.Frontend.Parser Fang.Equality.Ordered.Certificate := do
  Fang.Frontend.expect "("
  Fang.Frontend.expect "fang-proof"
  let version ← Fang.Frontend.natural
  if version != 8 then Fang.Frontend.fail "unsupported: expanded certificate version"
  Fang.Frontend.expect "("
  Fang.Frontend.expect "preprocessing"
  Fang.Frontend.expect v8Marker
  Fang.Frontend.expect ")"
  let (steps, finalId) ← Fang.EqualityOrderedCertificateInput.nodes fuel 0
  Fang.Frontend.expect ")"
  if (← Fang.Frontend.peek).isSome then Fang.Frontend.fail "invalid-certificate: trailing tokens"
  pure { steps, final := finalId }

def decodeV8 (proof : String) : Except String Fang.Equality.Ordered.Certificate := do
  let tokens ← Fang.Frontend.tokenize proof
  let (result, _) ← v8Certificate (tokens.length + 1) { tokens, endOffset := proof.utf8ByteSize }
  pure result

def decodesV8 (proof : String) : Bool :=
  match decodeV8 proof with
  | .ok _ => true
  | .error _ => false

/-- Envelope, signature gate and ordered check for a prepared problem. The
    axiom-only `accepts` supplies the problem from ExpandedReplay; a signed-task
    entry can pass its own prepared problem to the same check. -/
def checkProblem (problem : Fang.Equality.Problem) (functions predicates : List Nat)
    (proof : String) : Except CertificateError Unit := do
  let parsed ← (decodeV8 proof).mapError .certificate
  if !(problem.all (Fang.EqualityCertificateInput.clauseWellFormed functions predicates)) ||
      !(Fang.EqualityOrderedCertificateInput.certificateWellFormed functions predicates parsed) then
    .error .signature
  else (Fang.Equality.Ordered.check problem parsed).mapError .inference

theorem checkProblem_success {problem functions predicates proof}
    (accepted : checkProblem problem functions predicates proof = .ok ()) :
    ∃ parsed, decodeV8 proof = .ok parsed ∧
      problem.all (Fang.EqualityCertificateInput.clauseWellFormed functions predicates) = true ∧
      Fang.EqualityOrderedCertificateInput.certificateWellFormed functions predicates parsed = true ∧
      Fang.Equality.Ordered.check problem parsed = .ok () := by
  unfold checkProblem at accepted
  cases parsedRun : decodeV8 proof with
  | error error => simp [parsedRun, Except.mapError, bind, Except.bind] at accepted
  | ok parsed =>
    simp only [parsedRun, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
    · rename_i valid
      have both : problem.all (Fang.EqualityCertificateInput.clauseWellFormed functions predicates) = true ∧
          Fang.EqualityOrderedCertificateInput.certificateWellFormed functions predicates parsed = true := by
        simpa using valid
      refine ⟨parsed, rfl, both.1, both.2, ?_⟩
      cases checked : Fang.Equality.Ordered.check problem parsed with
      | error error => simp [checked] at accepted
      | ok value => cases value; rfl

theorem checkProblem_certificate_error {problem functions predicates proof message}
    (rejected : decodeV8 proof = .error message) :
    checkProblem problem functions predicates proof = .error (.certificate message) := by
  simp [checkProblem, rejected, Except.mapError, bind, Except.bind]

#print axioms Fang.TptpCandidate.FullFof.Integration.checkProblem_success
#print axioms Fang.TptpCandidate.FullFof.Integration.checkProblem_certificate_error

end Fang.TptpCandidate.FullFof.Integration
