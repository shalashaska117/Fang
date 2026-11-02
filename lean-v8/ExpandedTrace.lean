/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Retained checked steps for a version-8 pair, with export names bound to the
   decoded original tables that actual preparation returns. -/
import ExpandedSap

namespace Fang.QuantifiedEqualityTstp.Expanded
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration

def legacyPrepared (prepared : ReplayPrepared) : FangQuantifiedEqualityReplay.Prepared :=
  ⟨prepared.problem, prepared.functionArities, prepared.predicateArities⟩

structure Output where
  prepared : ReplayPrepared
  certificate : Fang.Equality.Ordered.Certificate
  clauses : List Fang.Equality.Clause

inductive BuildError where
  | replay : ReplayError → BuildError
  | certificate : String → BuildError
  | signature
  | inference : Fang.Equality.TraceError → BuildError

def WellFormed (prepared : ReplayPrepared) (certificate : Fang.Equality.Ordered.Certificate) : Bool :=
  prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed
      prepared.functionArities prepared.predicateArities) &&
    Fang.EqualityOrderedCertificateInput.certificateWellFormed
      prepared.functionArities prepared.predicateArities certificate

/-- The same replay, envelope decoder, signature gate and ordered step checker
    as `accepts`, with the checked clauses retained. No rule is reimplemented. -/
def build (bytes : List UInt8) (maximumBytes : Nat) (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except BuildError Output :=
  match prepare bytes maximumBytes limits maximumPredicates maximumLiterals with
  | .error reason => .error (.replay reason)
  | .ok prepared =>
    match decodeV8 proof with
    | .error reason => .error (.certificate reason)
    | .ok certificate =>
      if WellFormed prepared certificate then
        match retain prepared.problem certificate with
        | .error reason => .error (.inference reason)
        | .ok clauses => .ok ⟨prepared, certificate, clauses⟩
      else .error .signature

theorem build_witness {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    prepare bytes maximumBytes limits maximumPredicates maximumLiterals = .ok output.prepared ∧
      decodeV8 proof = .ok output.certificate ∧ WellFormed output.prepared output.certificate = true ∧
      retain output.prepared.problem output.certificate = .ok output.clauses := by
  cases preparedRun : prepare bytes maximumBytes limits maximumPredicates maximumLiterals with
  | error reason => simp [build, preparedRun] at success
  | ok prepared =>
    cases decoded : decodeV8 proof with
    | error reason => simp [build, preparedRun, decoded] at success
    | ok certificate =>
      by_cases valid : WellFormed prepared certificate = true
      · cases retained : retain prepared.problem certificate with
        | error reason => simp [build, preparedRun, decoded, valid, retained] at success
        | ok clauses =>
          simp [build, preparedRun, decoded, valid, retained] at success
          subst success
          exact ⟨rfl, rfl, valid, retained⟩
      · simp [build, preparedRun, decoded, valid] at success

theorem build_check {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    Fang.Equality.Ordered.check output.prepared.problem output.certificate = .ok () := by
  rw [← retain_erases, (build_witness success).2.2.2]
  rfl

theorem build_original_unsat {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes :=
  prepare_check_original_unsat (build_witness success).1 output.certificate (build_check success)

/-- A successful build is exactly an accepted version-8 pair. -/
theorem build_accepts {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok () := by
  obtain ⟨preparedRun, decoded, wellFormed, _⟩ := build_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  simp [accepts, checkProblem, preparedRun, decoded, wellFormed, build_check success,
    Except.mapError, bind, Except.bind]

def rows (output : Output) : List Derivation.Row := output.certificate.steps.zip output.clauses

theorem build_rows {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    Derivation.Checked output.prepared.problem [] (rows output) ∧
      (rows output).map Prod.snd = output.clauses := by
  obtain ⟨checkedSteps, _, _, _⟩ := retain_witness (build_witness success).2.2.2
  obtain ⟨values, checked, sameSteps, sameClauses⟩ := Derivation.checkSteps_rows checkedSteps
  simp only [List.nil_append] at sameClauses
  have paired : rows output = values := by
    rw [rows, ← sameSteps, ← sameClauses, Derivation.zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameClauses⟩

theorem build_row_checked {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : rows output = leading ++ value :: rest) :
    Fang.Equality.Ordered.checkStep output.prepared.problem (leading.map Prod.snd) value.1 = .ok value.2 := by
  have checked := (build_rows success).1
  rw [position] at checked
  simpa using checked.row

/-- Names are checked against the original tables carried by actual preparation. -/
def attach (output : Output) (functions : List Frontend.Symbol) : Except String Body.Names :=
  Naming.check output.prepared.original.functions output.prepared.original.predicates
    (legacyPrepared output.prepared) functions

theorem attach_spec {output functions names} (success : attach output functions = .ok names) :
    Naming.Checked output.prepared.original.functions output.prepared.original.predicates
      (legacyPrepared output.prepared) names :=
  Naming.check_spec success

/-- SAP for the group of a built pair under attached names. -/
theorem build_group_sap {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
    {functions names} (named : attach output functions = .ok names)
    {formula} (formulaRun : Group.groupFormula names output.prepared.problem = .ok formula)
    (satisfiable : CnfBoolean.BytesSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨preparedRun, _, wellFormed, _⟩ := build_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  exact group_sap preparedRun (attach_spec named) wellFormed.1 formulaRun satisfiable

#print axioms Fang.QuantifiedEqualityTstp.Expanded.build_witness
#print axioms Fang.QuantifiedEqualityTstp.Expanded.build_check
#print axioms Fang.QuantifiedEqualityTstp.Expanded.build_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.Expanded.build_accepts
#print axioms Fang.QuantifiedEqualityTstp.Expanded.build_rows
#print axioms Fang.QuantifiedEqualityTstp.Expanded.build_row_checked
#print axioms Fang.QuantifiedEqualityTstp.Expanded.attach_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.build_group_sap

end Fang.QuantifiedEqualityTstp.Expanded
