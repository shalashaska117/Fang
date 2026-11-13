/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Retained certificate steps and checked export names over named preparation. -/
import NamedSap

namespace Fang.QuantifiedEqualityTstp.NamedExport
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration
open Expanded (Output WellFormed rows legacyPrepared)

inductive BuildError where
  | replay : Named.NamedError → BuildError
  | certificate : String → BuildError
  | signature
  | inference : Fang.Equality.TraceError → BuildError

/-- The same replay, envelope decoder, signature gate and ordered step checker
    as `accepts`, with the checked clauses retained. No rule is reimplemented. -/
def build (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except BuildError Expanded.Output :=
  match Named.prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals with
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

theorem build_witness {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Named.prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals = .ok output.prepared ∧
      decodeV8 proof = .ok output.certificate ∧ WellFormed output.prepared output.certificate = true ∧
      retain output.prepared.problem output.certificate = .ok output.clauses := by
  cases preparedRun : Named.prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals with
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

theorem build_check {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Fang.Equality.Ordered.check output.prepared.problem output.certificate = .ok () := by
  rw [← retain_erases, (build_witness success).2.2.2]
  rfl

theorem build_original_unsat {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes :=
  Named.prepareNamed_check_original_unsat (build_witness success).1 output.certificate (build_check success)

/-- A successful build is exactly an accepted version-8 pair. -/
theorem build_accepts {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Named.acceptsNamed limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok () := by
  obtain ⟨preparedRun, decoded, wellFormed, _⟩ := build_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  simp [Named.acceptsNamed, checkProblem, preparedRun, decoded, wellFormed, build_check success,
    Except.mapError, bind, Except.bind]

def rows (output : Expanded.Output) : List Derivation.Row := output.certificate.steps.zip output.clauses

theorem build_rows {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Derivation.Checked output.prepared.problem [] (rows output) ∧
      (rows output).map Prod.snd = output.clauses := by
  obtain ⟨checkedSteps, _, _, _⟩ := retain_witness (build_witness success).2.2.2
  obtain ⟨values, checked, sameSteps, sameClauses⟩ := Derivation.checkSteps_rows checkedSteps
  simp only [List.nil_append] at sameClauses
  have paired : rows output = values := by
    rw [rows, ← sameSteps, ← sameClauses, Derivation.zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameClauses⟩

theorem build_row_checked {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : rows output = leading ++ value :: rest) :
    Fang.Equality.Ordered.checkStep output.prepared.problem (leading.map Prod.snd) value.1 = .ok value.2 := by
  have checked := (build_rows success).1
  rw [position] at checked
  simpa using checked.row

/-- Names are checked against the original tables carried by actual preparation. -/
def attach (output : Expanded.Output) (proposed : Body.Names) : Except String Body.Names :=
  check output.prepared.original.functions output.prepared.original.predicates
    (legacyPrepared output.prepared) proposed

theorem attach_spec {output proposed names} (success : attach output proposed = .ok names) :
    Checked output.prepared.original.functions output.prepared.original.predicates
      (legacyPrepared output.prepared) names :=
  check_spec success

/-- SAP for the group of a built pair under attached names. -/
theorem build_group_sap {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output)
    {proposed names} (named : attach output proposed = .ok names)
    {formula} (formulaRun : Group.groupFormula names output.prepared.problem = .ok formula)
    (satisfiable : CnfBoolean.BytesSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨preparedRun, _, wellFormed, _⟩ := build_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  exact group_sap preparedRun (attach_spec named) wellFormed.1 formulaRun satisfiable

end Fang.QuantifiedEqualityTstp.NamedExport
