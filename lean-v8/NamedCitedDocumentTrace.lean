/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Retained ordered traces for the existing cited signed-bundle checker.
   The certificate is replayed against the selected, cited task, without
   converting the original bundle into a synthetic single source file. -/
import NamedCitedDepth
import NamedGoalDocumentDepth

namespace Fang.TptpCandidate.CitedDocument
open Aeneas.Std FullFof
open Roles.Bundle Roles.Bundle.V3 Roles.Bundle.V3.Depth
open Fang.QuantifiedEqualityTstp
open FangQuantifiedEqualityReplay (bind_success mapError_success)

structure Output where
  prepared : BundleGoalPrepared
  certificate : Fang.Equality.Ordered.Certificate
  clauses : List Fang.Equality.Clause

inductive BuildError where
  | task : Named.CitedError → BuildError
  | certificate : String → BuildError
  | signature
  | inference : Fang.Equality.TraceError → BuildError

def wellFormed (replay : Roles.Signed.SignedPrepared)
    (certificate : Fang.Equality.Ordered.Certificate) : Bool :=
  GoalDocument.NamedDepth.GoalWellFormed replay certificate

def build (frame : Frame) (files : List (Coverage.Key × List UInt8))
    (maximumBytes index : Nat) (cited : List Coverage.Item) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except BuildError Output :=
  match Named.prepareGoalCited frame files maximumBytes index cited limits threshold maximumPredicates maximumLiterals with
  | .error error => .error (.task error)
  | .ok prepared =>
    match Integration.decodeV8 proof with
    | .error error => .error (.certificate error)
    | .ok certificate =>
      if wellFormed prepared.replay certificate then
        match retain prepared.replay.problem certificate with
        | .error error => .error (.inference error)
        | .ok clauses => .ok ⟨prepared, certificate, clauses⟩
      else .error .signature

theorem build_witness {frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Named.prepareGoalCited frame files maximumBytes index cited limits threshold maximumPredicates maximumLiterals = .ok output.prepared ∧
      Integration.decodeV8 proof = .ok output.certificate ∧
      wellFormed output.prepared.replay output.certificate = true ∧
      retain output.prepared.replay.problem output.certificate = .ok output.clauses := by
  cases preparedRun : Named.prepareGoalCited frame files maximumBytes index cited limits threshold maximumPredicates maximumLiterals with
  | error reason => simp [build, preparedRun] at success
  | ok prepared =>
    cases decoded : Integration.decodeV8 proof with
    | error reason => simp [build, preparedRun, decoded] at success
    | ok certificate =>
      by_cases valid : wellFormed prepared.replay certificate = true
      · cases retained : retain prepared.replay.problem certificate with
        | error reason => simp [build, preparedRun, decoded, valid, retained] at success
        | ok clauses =>
          simp [build, preparedRun, decoded, valid, retained] at success
          subst success
          exact ⟨rfl, rfl, valid, retained⟩
      · simp [build, preparedRun, decoded, valid] at success

theorem build_check {frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Fang.Equality.Ordered.check output.prepared.replay.problem output.certificate = .ok () := by
  rw [← retain_erases, (build_witness success).2.2.2]
  rfl

theorem build_accepts {frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Named.acceptsGoalCited frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals =
      .ok output.prepared.item := by
  obtain ⟨preparedRun, decoded, valid, _⟩ := build_witness success
  simp only [wellFormed, GoalDocument.NamedDepth.GoalWellFormed, Bool.and_eq_true] at valid
  simp [Named.acceptsGoalCited, Integration.checkProblem, preparedRun, decoded, valid, build_check success,
    Except.mapError, Bind.bind, Except.bind]
  rfl

/-- The retained trace keeps the selected goal's original bundle coordinates.
    The selected task is rebuilt from the cited items and includes its distinct
    object constraints, exactly as in the existing checker. -/
theorem source_task {frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ∃ (read : BundleRead) (entry : Roles.Bytes.Entry) (input : Roles.Numeric.SignedInput) (position : Nat)
      (before : List Roles.Numeric.RoleRow) (goal : Roles.Numeric.RoleRow) (after : List Roles.Numeric.RoleRow)
      (keptEntry : Roles.Bytes.Entry) (task : List Roles.Numeric.SignedNumeric),
      readBundle frame files maximumBytes = .ok read ∧
      (goalItems read.bundle read.items)[index]? = some (output.prepared.item, entry) ∧
      Roles.Numeric.readSigned (entriesOf read.bundle (keptItems read.items cited (some output.prepared.item))) = some input ∧
      (goalItems read.bundle (keptItems read.items cited (some output.prepared.item)))[position]? =
        some (output.prepared.item, keptEntry) ∧
      (Roles.Signed.goalSplits input)[position]? = some (before, goal, after) ∧
      Roles.Numeric.goalTask before goal after = some task ∧
      Roles.Signed.replayNamedTask input
        (task ++ Roles.Bundle.V2.distinctItems input read.bundle (keptItems read.items cited (some output.prepared.item)))
        limits threshold maximumPredicates maximumLiterals = .ok output.prepared.replay :=
  Named.prepareGoalCited_witness (build_witness success).1

theorem build_entails {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    GoalEntailed frame files maximumBytes bundleFuel output.prepared.item :=
  Named.acceptsGoalCited_entails frameSound (build_accepts success)

def expandedOutput (output : Output) : Expanded.Output :=
  ⟨⟨Roles.Signed.tables output.prepared.replay.input, output.prepared.replay.problem,
    output.prepared.replay.functionArities, output.prepared.replay.predicateArities⟩,
    output.certificate, output.clauses⟩

theorem rows_checked {frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Derivation.Checked output.prepared.replay.problem [] (Expanded.rows (expandedOutput output)) ∧
      (Expanded.rows (expandedOutput output)).map Prod.snd = output.clauses := by
  obtain ⟨checkedSteps, _, _, _⟩ := retain_witness (build_witness success).2.2.2
  obtain ⟨values, checked, sameSteps, sameClauses⟩ := Derivation.checkSteps_rows checkedSteps
  simp only [List.nil_append] at sameClauses
  have paired : Expanded.rows (expandedOutput output) = values := by
    show output.certificate.steps.zip output.clauses = values
    rw [← sameSteps, ← sameClauses, Derivation.zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameClauses⟩

theorem final_row_empty {frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ((Expanded.rows (expandedOutput output))[output.certificate.final]?).map Prod.snd = some [] ∧
      output.certificate.final + 1 = (Expanded.rows (expandedOutput output)).length := by
  obtain ⟨_, _, last, empty⟩ := retain_witness (build_witness success).2.2.2
  have clauses := (rows_checked success).2
  have clausesLength := congrArg List.length clauses
  simp only [List.length_map] at clausesLength
  refine ⟨?_, by rw [clausesLength]; exact last⟩
  rw [← clauses] at empty
  simpa using empty

end Fang.TptpCandidate.CitedDocument
