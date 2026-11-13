/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Retained checked steps for a bundle pair: `ExpandedTrace.build` with the
   bundle preparation in place of the single-file one, export names checked
   against the original tables with distinct objects renamed, and SAP for the
   group formula with respect to the revision-2 bundle meaning. -/
import ExpandedTrace
import BundleFastFramer
import BundleSourceRow

namespace Fang.QuantifiedEqualityTstp.Expanded.Bundle

open Aeneas.Std
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration
open Fang.QuantifiedCertificate FangQuantifiedPipeline
open FangQuantifiedEqualityReplay (bind_success mapError_success)
open Fang.TptpCandidate.FullFof.Coverage (Key Item expand declarationsOf)
open Fang.TptpCandidate.FullFof.Coverage.BundleV8
open Fang.QuantifiedEqualityTstp.Expanded

inductive BundleBuildError where
  | prepare : BundleReplayError → BundleBuildError
  | certificate : String → BundleBuildError
  | signature
  | inference : Fang.Equality.TraceError → BundleBuildError

/-- `ExpandedTrace.build` over a sealed bundle, with the linear framer. -/
def buildBundle (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleBuildError Output :=
  match prepareBundleFast files maximumBytes limits maximumPredicates maximumLiterals with
  | .error reason => .error (.prepare reason)
  | .ok prepared =>
    match decodeV8 proof with
    | .error reason => .error (.certificate reason)
    | .ok certificate =>
      if WellFormed prepared certificate then
        match retain prepared.problem certificate with
        | .error reason => .error (.inference reason)
        | .ok clauses => .ok ⟨prepared, certificate, clauses⟩
      else .error .signature

theorem buildBundle_witness {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    prepareBundle files maximumBytes limits maximumPredicates maximumLiterals = .ok output.prepared ∧
      decodeV8 proof = .ok output.certificate ∧ WellFormed output.prepared output.certificate = true ∧
      retain output.prepared.problem output.certificate = .ok output.clauses := by
  rw [← prepareBundleFast_eq]
  cases preparedRun : prepareBundleFast files maximumBytes limits maximumPredicates maximumLiterals with
  | error reason => simp [buildBundle, preparedRun] at success
  | ok prepared =>
    cases decoded : decodeV8 proof with
    | error reason => simp [buildBundle, preparedRun, decoded] at success
    | ok certificate =>
      by_cases valid : WellFormed prepared certificate = true
      · cases retained : retain prepared.problem certificate with
        | error reason => simp [buildBundle, preparedRun, decoded, valid, retained] at success
        | ok clauses =>
          simp [buildBundle, preparedRun, decoded, valid, retained] at success
          subst success
          exact ⟨rfl, rfl, valid, retained⟩
      · simp [buildBundle, preparedRun, decoded, valid] at success

theorem buildBundle_check {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    Fang.Equality.Ordered.check output.prepared.problem output.certificate = .ok () := by
  rw [← retain_erases, (buildBundle_witness success).2.2.2]
  rfl

/-- A successful build is an accepted bundle pair (the forward direction only). -/
theorem buildBundle_accepts {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok () := by
  obtain ⟨preparedRun, decoded, wellFormed, _⟩ := buildBundle_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  simp [acceptsBundle, checkProblem, preparedRun, decoded, wellFormed, buildBundle_check success,
    Except.mapError, Bind.bind, Except.bind]

theorem buildBundle_refuted {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    BundleRefuted files maximumBytes bundleFuel :=
  acceptsBundle_refuted (buildBundle_accepts success)

theorem buildBundle_rows {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    Derivation.Checked output.prepared.problem [] (rows output) ∧
      (rows output).map Prod.snd = output.clauses := by
  obtain ⟨checkedSteps, _, _, _⟩ := retain_witness (buildBundle_witness success).2.2.2
  obtain ⟨values, checked, sameSteps, sameClauses⟩ := Derivation.checkSteps_rows checkedSteps
  simp only [List.nil_append] at sameClauses
  have paired : rows output = values := by
    rw [rows, ← sameSteps, ← sameClauses, Derivation.zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameClauses⟩

theorem buildBundle_row_checked {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : rows output = leading ++ value :: rest) :
    Fang.Equality.Ordered.checkStep output.prepared.problem (leading.map Prod.snd) value.1 = .ok value.2 := by
  have checked := (buildBundle_rows success).1
  rw [position] at checked
  simpa using checked.row

/-- What the source rows restate: the framed bundle, its expansion and the
    declarations it selects, whose `readInput` tables are the original tables
    of the prepared problem; the generated distinct-object clauses follow. -/
theorem buildBundle_sources {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    ∃ bundle items input, Coverage.FramerV2.frameBundle files maximumBytes = .ok bundle ∧
      Coverage.FramerV2.wellShaped bundle bundleFuel = true ∧ expand bundle bundleFuel = .ok items ∧
      readInput (declarationsOf bundle items) = some input ∧
      output.prepared.original = withGenerated input
        (Coverage.distinctAxioms input.predicates.length (objectIds input (declarationsOf bundle items))) := by
  obtain ⟨numeric, numericRun, replayRun⟩ := bind_success (buildBundle_witness success).1
  obtain ⟨bundle, items, input, framed, shaped, expanded, encoded, same⟩ :=
    bundleNumeric_witness (mapError_success numericRun)
  obtain ⟨_, _, _, _, original, _⟩ := replayFrom_witness (mapError_success replayRun)
  exact ⟨bundle, items, input, framed, shaped, expanded, encoded, original.trans same⟩

/-- The model direction of `replayFrom_check_unsat`: a model of the numeric
    input gives a model of the prepared problem. -/
theorem replayFrom_models {numeric limits maximumPredicates maximumLiterals prepared}
    (below : ∀ value ∈ numeric.declarations, DeclarationBelow numeric.functions.length value)
    (success : replayFrom numeric limits maximumPredicates maximumLiterals = .ok prepared)
    (satisfiable : numeric.Satisfiable) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  obtain ⟨encoded, transformed, blocks, ordinary, _, inputRun, skolemRun, steps, layout, converted⟩ :=
    replayFrom_witness success
  obtain ⟨D, nonempty, original, holds⟩ := satisfiable
  let : Nonempty D := nonempty
  obtain ⟨valid, _, slot, _, functions, _⟩ := transport_tables inputRun
  have count : encoded.signature.functions.val.length = numeric.functions.length := by
    simpa only [List.length_map] using congrArg List.length functions
  have bounded : ProblemBelow encoded.signature.functions.val.length (retained numeric.declarations) := by
    rw [count]
    exact retained_below below
  have originalHolds := transport_models inputRun holds
  have reservedHolds :
      (retained numeric.declarations).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original) ∧
      SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
        encoded.declarations.val := by
    rw [slot, ← reserve_interpretation]
    exact originalHolds
  obtain ⟨extended, preserved, grouped⟩ := skolem_actual_problem_models skolemRun
    (retained numeric.declarations) bounded blocks steps
    (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
  have groupedModel := grouped.mpr reservedHolds
  have mixedModel : ordinary.Models extended := (mixedLayout_models layout extended).mpr
    ((FangQuantifiedPipeline.models_append extended _ _).mp groupedModel)
  have equalityModel := (FangQuantifiedEquality.actualProblem_models original extended
    encoded.reservation encoded.signature.functions.val.length valid preserved converted).mp mixedModel
  exact ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation original extended, equalityModel⟩

/-- Every model of the sealed bundle in which different distinct objects
    denote different elements gives a model of the prepared problem. -/
theorem prepareBundle_models {files maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepareBundle files maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (satisfiable : Coverage.FramerV2.ByteBundleSatisfiable files maximumBytes bundleFuel) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  obtain ⟨numeric, numericRun, replayRun⟩ := bind_success success
  have numericOk := mapError_success numericRun
  have numericSatisfiable : numeric.Satisfiable :=
    Classical.byContradiction fun refuted => bundleNumeric_unsat numericOk refuted satisfiable
  exact replayFrom_models (bundleNumeric_below numericOk) (mapError_success replayRun) numericSatisfiable

/-- `attach` with the objects renamed. The names are checked against the
    renamed table; `Naming.check` rejects any collision. -/
def attachBundle (output : Output) (stem : String) (functions : List Frontend.Symbol) :
    Except String Body.Names :=
  Naming.check (renameObjects stem output.prepared.original.functions) output.prepared.original.predicates
    (legacyPrepared output.prepared) functions

theorem attachBundle_spec {output stem functions names} (success : attachBundle output stem functions = .ok names) :
    Naming.Checked (renameObjects stem output.prepared.original.functions) output.prepared.original.predicates
      (legacyPrepared output.prepared) names :=
  Naming.check_spec success

/-- SAP for the group of a built bundle pair under attached names: if the
    sealed bundle has a model in which different distinct objects denote
    different elements, the group formula holds in some source model. -/
theorem bundle_group_sap {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
    {stem functions names} (named : attachBundle output stem functions = .ok names)
    {formula} (formulaRun : Group.groupFormula names output.prepared.problem = .ok formula)
    (satisfiable : Coverage.FramerV2.ByteBundleSatisfiable files maximumBytes bundleFuel) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨preparedRun, _, wellFormed, _⟩ := buildBundle_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  obtain ⟨D, nonempty, model, holds⟩ := prepareBundle_models preparedRun satisfiable
  have named' := namedModel_models (prepared := legacyPrepared output.prepared) (attachBundle_spec named)
    wellFormed.1 model holds
  exact ⟨D, nonempty, namedModel names model,
    ((Group.groupFormula_spec formulaRun).2.2 (namedModel names model)).mpr named'⟩

#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.buildBundle_witness
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.buildBundle_check
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.buildBundle_accepts
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.buildBundle_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.buildBundle_rows
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.buildBundle_row_checked
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.buildBundle_sources
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.replayFrom_models
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.prepareBundle_models
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.attachBundle_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bundle_group_sap

end Fang.QuantifiedEqualityTstp.Expanded.Bundle
