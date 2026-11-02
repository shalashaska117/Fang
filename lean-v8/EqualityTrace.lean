/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Retain the existing ordered equality checker's actual clause sequence. -/
import EqualityOriginalCertificate

namespace Fang.QuantifiedEqualityTstp
open Equality

/-- The same checker call and endpoint guards as Ordered.check, with its
    checked clauses retained for later proof output. No rule is reimplemented. -/
def retain (problem : Equality.Problem) (certificate : Ordered.Certificate) :
    Except TraceError (List Equality.Clause) := do
  let checked ← Ordered.checkSteps problem [] certificate.steps
  if certificate.final + 1 = checked.length then
    if checked[certificate.final]? = some [] then .ok checked else .error .finalNotEmpty
  else .error .finalIndex

theorem retain_erases (problem : Equality.Problem) (certificate : Ordered.Certificate) :
    (retain problem certificate).map (fun _ => ()) = Ordered.check problem certificate := by
  cases checked : Ordered.checkSteps problem [] certificate.steps with
  | error reason => simp [retain, Ordered.check, checked, Except.map, Bind.bind, Except.bind]
  | ok clauses =>
    by_cases last : certificate.final + 1 = clauses.length
    · by_cases empty : clauses[certificate.final]? = some []
      · simp [retain, Ordered.check, checked, last, empty, Except.map, Bind.bind, Except.bind]
      · simp [retain, Ordered.check, checked, last, empty, Except.map, Bind.bind, Except.bind]
    · simp [retain, Ordered.check, checked, last, Except.map, Bind.bind, Except.bind]

theorem retain_witness {problem certificate clauses}
    (success : retain problem certificate = .ok clauses) :
    Ordered.checkSteps problem [] certificate.steps = .ok clauses ∧
      clauses.length = certificate.steps.length ∧
      certificate.final + 1 = clauses.length ∧ clauses[certificate.final]? = some [] := by
  cases checked : Ordered.checkSteps problem [] certificate.steps with
  | error reason => simp [retain, checked, Bind.bind, Except.bind] at success
  | ok result =>
    simp only [retain, checked, Bind.bind, Except.bind] at success
    split at success
    next last =>
      split at success
      next empty =>
        cases success
        exact ⟨rfl, by simpa using Ordered.checkSteps_length problem certificate.steps [] clauses checked,
          last, empty⟩
      next nonempty => contradiction
    next notLast => contradiction

structure Output where
  prepared : FangQuantifiedEqualityReplay.Prepared
  certificate : Ordered.Certificate
  clauses : List Equality.Clause

/-- Preserve the version-7 decoder and both complete signature guards. The
    preprocessing, decoder and ordered step checker are each called once. -/
def build (input proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    Except FangQuantifiedEqualityCertificate.Error Output := do
  let prepared ← (FangQuantifiedEqualityReplay.prepare input limits
    maximumPredicates maximumLiterals).mapError .replay
  let certificate ← (FangQuantifiedEqualityCertificate.decodeCertificate proof).mapError
    (fun reason => .prepared (.certificate reason))
  if !(prepared.problem.all (EqualityCertificateInput.clauseWellFormed
        prepared.functionArities prepared.predicateArities)) ||
      !(EqualityOrderedCertificateInput.certificateWellFormed
        prepared.functionArities prepared.predicateArities certificate) then
    .error (.prepared .signature)
  else
    let clauses ← (retain prepared.problem certificate).mapError
      (fun reason => .prepared (.inference reason))
    pure ⟨prepared, certificate, clauses⟩

theorem build_witness {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output) :
    FangQuantifiedEqualityReplay.prepare input limits maximumPredicates maximumLiterals = .ok output.prepared ∧
      FangQuantifiedEqualityCertificate.decodeCertificate proof = .ok output.certificate ∧
      output.prepared.problem.all (EqualityCertificateInput.clauseWellFormed
        output.prepared.functionArities output.prepared.predicateArities) = true ∧
      EqualityOrderedCertificateInput.certificateWellFormed
        output.prepared.functionArities output.prepared.predicateArities output.certificate = true ∧
      retain output.prepared.problem output.certificate = .ok output.clauses := by
  cases preparedAt : FangQuantifiedEqualityReplay.prepare input limits maximumPredicates maximumLiterals with
  | error reason => simp [build, preparedAt, Except.mapError, Bind.bind, Except.bind] at success
  | ok prepared =>
    cases decoded : FangQuantifiedEqualityCertificate.decodeCertificate proof with
    | error reason => simp [build, preparedAt, decoded, Except.mapError, Bind.bind, Except.bind] at success
    | ok certificate =>
      simp only [build, preparedAt, decoded, Except.mapError, Bind.bind, Except.bind] at success
      split at success
      · cases success
      · rename_i valid
        have both : prepared.problem.all (EqualityCertificateInput.clauseWellFormed
            prepared.functionArities prepared.predicateArities) = true ∧
            EqualityOrderedCertificateInput.certificateWellFormed
              prepared.functionArities prepared.predicateArities certificate = true := by
          simpa using valid
        cases retained : retain prepared.problem certificate with
        | error reason => simp [retained] at success
        | ok clauses =>
          have same : (⟨prepared, certificate, clauses⟩ : Output) = output := by
            simpa [retained, Except.mapError, Bind.bind, Except.bind, pure, Except.pure] using success
          subst output
          exact ⟨rfl,rfl,both.1,both.2,retained⟩

theorem build_accepted {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output) :
    FangQuantifiedEqualityCertificate.accepts input proof limits maximumPredicates maximumLiterals = .ok () := by
  obtain ⟨preparedAt,decoded,problemValid,certificateValid,retained⟩ := build_witness success
  have checked : Ordered.check output.prepared.problem output.certificate = .ok () := by
    rw [← retain_erases, retained]
    rfl
  simp [FangQuantifiedEqualityCertificate.accepts, preparedAt,
    FangQuantifiedEqualityCertificate.checkPrepared, decoded, problemValid, certificateValid,
    checked, Except.mapError, Bind.bind, Except.bind]

theorem build_endpoint {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output) :
    Ordered.checkSteps output.prepared.problem [] output.certificate.steps = .ok output.clauses ∧
      output.clauses.length = output.certificate.steps.length ∧
      output.certificate.final + 1 = output.clauses.length ∧
      output.clauses[output.certificate.final]? = some [] :=
  retain_witness (build_witness success).2.2.2.2

theorem build_clauses_valid {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output)
    {D : Type} (model : Interpretation D) (original : models model output.prepared.problem) :
    ∀ clause ∈ output.clauses, clauseValid model clause :=
  Ordered.checkSteps_sound model output.prepared.problem output.certificate.steps [] output.clauses
    original (by simp) (build_endpoint success).1

theorem build_original_unsat {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output) :
    ¬ NamedQuantifiedEquality.Grammar.BytesSatisfiable (Source.Grammar.spelling input) :=
  FangQuantifiedEqualityCertificate.accepts_original_unsat (build_accepted success)

#print axioms Fang.QuantifiedEqualityTstp.retain_erases
#print axioms Fang.QuantifiedEqualityTstp.retain_witness
#print axioms Fang.QuantifiedEqualityTstp.build_witness
#print axioms Fang.QuantifiedEqualityTstp.build_accepted
#print axioms Fang.QuantifiedEqualityTstp.build_endpoint
#print axioms Fang.QuantifiedEqualityTstp.build_clauses_valid
#print axioms Fang.QuantifiedEqualityTstp.build_original_unsat

end Fang.QuantifiedEqualityTstp
