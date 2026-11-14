import CitedModels

namespace Fang.TptpCandidate.CitedDocument.Inputs
open FullFof Roles.Bundle Roles.Bundle.V3 Roles.Bundle.V3.Depth
open Fang.QuantifiedEqualityTstp

structure Output where
  prepared : Roles.Signed.SignedPrepared
  certificate : Fang.Equality.Ordered.Certificate
  clauses : List Fang.Equality.Clause

def build (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (cited : List Coverage.Item) (proof : String) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except CitedDocument.BuildError Output :=
  match Named.prepareInputsCited frame files maximumBytes cited limits threshold maximumPredicates maximumLiterals with
  | .error error => .error (.task error)
  | .ok prepared =>
    match Integration.decodeV8 proof with
    | .error error => .error (.certificate error)
    | .ok certificate =>
      if CitedDocument.wellFormed prepared certificate then
        match retain prepared.problem certificate with
        | .error error => .error (.inference error)
        | .ok clauses => .ok ⟨prepared, certificate, clauses⟩
      else .error .signature

theorem build_witness {frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Named.prepareInputsCited frame files maximumBytes cited limits threshold maximumPredicates maximumLiterals = .ok output.prepared ∧
      Integration.decodeV8 proof = .ok output.certificate ∧
      CitedDocument.wellFormed output.prepared output.certificate = true ∧
      retain output.prepared.problem output.certificate = .ok output.clauses := by
  cases preparedRun : Named.prepareInputsCited frame files maximumBytes cited limits threshold maximumPredicates maximumLiterals with
  | error reason => simp [build, preparedRun] at success
  | ok prepared =>
    cases decoded : Integration.decodeV8 proof with
    | error reason => simp [build, preparedRun, decoded] at success
    | ok certificate =>
      by_cases valid : CitedDocument.wellFormed prepared certificate = true
      · cases retained : retain prepared.problem certificate with
        | error reason => simp [build, preparedRun, decoded, valid, retained] at success
        | ok clauses =>
          simp [build, preparedRun, decoded, valid, retained] at success
          subst success
          exact ⟨rfl, rfl, valid, retained⟩
      · simp [build, preparedRun, decoded, valid] at success

theorem build_check {frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Fang.Equality.Ordered.check output.prepared.problem output.certificate = .ok () := by
  rw [← retain_erases, (build_witness success).2.2.2]
  rfl

theorem build_accepts {frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Named.acceptsInputsCited frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok () := by
  obtain ⟨preparedRun, decoded, valid, _⟩ := build_witness success
  simp only [CitedDocument.wellFormed, GoalDocument.NamedDepth.GoalWellFormed, Bool.and_eq_true] at valid
  simp [Named.acceptsInputsCited, Integration.checkProblem, preparedRun, decoded, valid, build_check success,
    Except.mapError, Bind.bind, Except.bind]

theorem build_unsat {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ByteUnsatisfiable frame files maximumBytes bundleFuel :=
  Named.acceptsInputsCited_unsat frameSound (build_accepts success)

def expandedOutput (output : Output) : Expanded.Output :=
  ⟨⟨Roles.Signed.tables output.prepared.input, output.prepared.problem,
    output.prepared.functionArities, output.prepared.predicateArities⟩, output.certificate, output.clauses⟩

theorem rows_checked {frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Derivation.Checked output.prepared.problem [] (Expanded.rows (expandedOutput output)) ∧
      (Expanded.rows (expandedOutput output)).map Prod.snd = output.clauses := by
  obtain ⟨checkedSteps, _, _, _⟩ := retain_witness (build_witness success).2.2.2
  obtain ⟨values, checked, sameSteps, sameClauses⟩ := Derivation.checkSteps_rows checkedSteps
  simp only [List.nil_append] at sameClauses
  have paired : Expanded.rows (expandedOutput output) = values := by
    show output.certificate.steps.zip output.clauses = values
    rw [← sameSteps, ← sameClauses, Derivation.zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameClauses⟩

theorem final_row_empty {frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals output}
    (success : build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ((Expanded.rows (expandedOutput output))[output.certificate.final]?).map Prod.snd = some [] ∧
      output.certificate.final + 1 = (Expanded.rows (expandedOutput output)).length := by
  obtain ⟨_, _, last, empty⟩ := retain_witness (build_witness success).2.2.2
  have clauses := (rows_checked success).2
  have clausesLength := congrArg List.length clauses
  simp only [List.length_map] at clausesLength
  refine ⟨?_, by rw [clausesLength]; exact last⟩
  rw [← clauses] at empty
  simpa using empty

theorem group_sap {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals output}
    (built : build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok output)
    {proposed names} (named : attachNames output.prepared proposed = .ok names)
    {formula} (formulaRun : Group.groupFormula names output.prepared.problem = .ok formula)
    (satisfiable : InputsModel frame files maximumBytes cited) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D), ∀ valuation, formula.Holds model valuation := by
  obtain ⟨preparedRun, _, wellFormed, _⟩ := build_witness built
  simp only [CitedDocument.wellFormed, GoalDocument.NamedDepth.GoalWellFormed, Bool.and_eq_true] at wellFormed
  obtain ⟨D, nonempty, model, holds⟩ := prepare_inputs_models frameSound preparedRun satisfiable
  exact ⟨D, nonempty, Expanded.namedModel names model,
    NamedExport.group_models (attachNames_spec named) wellFormed.1 formulaRun model holds⟩

#print axioms build_witness
#print axioms build_check
#print axioms build_accepts
#print axioms build_unsat
#print axioms rows_checked
#print axioms final_row_empty
#print axioms group_sap
end Fang.TptpCandidate.CitedDocument.Inputs
