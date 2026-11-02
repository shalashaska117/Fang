/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Bundle TSTP documents for any sound frame function. `buildBundle`, `bundleDocumentOf`, `bundleDocument` and `exportBundleDocument` are the `Bundle` definitions of `BundleTrace` and `BundleDocument` with the frame as a parameter, both where the pair is prepared and where the bundle is framed again for the source rows; with framer revision 2 as the frame they are those definitions. The trace and document theorems are restated for every sound frame, with SAP against `FramerLimit.ByteBundleSatisfiable` for that frame. A printed source row holds one formula and is read back by the gated framer, so the per-file limit does not change that check. `exportBundleDocument_hashed_refuted` gives the refutation for the hashed framer at any limit, over the list framer with that limit. -/
import BundleReplayLimit
import BundleDocument

namespace Fang.QuantifiedEqualityTstp.Expanded.BundleLimit

open Aeneas.Std
open Fang.TptpCandidate Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration TstpText
open Fang.QuantifiedCertificate FangQuantifiedPipeline
open FangQuantifiedEqualityReplay (bind_success mapError_success)
open Fang.TptpCandidate.FullFof.Coverage (Key Item Bundle expand declarationsOf)
open Fang.TptpCandidate.FullFof.Coverage.FramerLimit (Frame FrameSound ByteBundleSatisfiable frameBundle
  frameBundleHashed)
open Fang.TptpCandidate.FullFof.Coverage.BundleLimit (prepareBundle acceptsBundle BundleRefuted
  bundleNumeric_witness bundleNumeric_unsat bundleNumeric_below acceptsBundle_refuted)
open Fang.TptpCandidate.FullFof.Coverage.BundleV8 (bundleFuel withGenerated objectIds replayFrom_witness)
open Fang.QuantifiedEqualityTstp.Expanded
open Fang.QuantifiedEqualityTstp.Expanded.Bundle (BundleBuildError attachBundle attachBundle_spec replayFrom_models
  bundleAssemble bundleSourceRows_spec RowsFrame sourceItem pathOf Paired rowBytes maximumRowBytes rows_read_bodies
  sourceItems_declarations source_of_bodies objectStem bundleExportFunctions)

/-! The trace: `BundleTrace` with the frame as a parameter. -/

def buildBundle (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleBuildError Output :=
  match prepareBundle frame files maximumBytes limits maximumPredicates maximumLiterals with
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

theorem buildBundle_revision_two (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    buildBundle Coverage.FramerV2.frameBundle files maximumBytes proof limits maximumPredicates maximumLiterals =
      Bundle.buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals := by
  unfold buildBundle Bundle.buildBundle
  rw [Coverage.BundleV8.prepareBundleFast_eq]
  -- The two definitions use distinct auxiliary match functions with equal bodies.
  rfl

theorem buildBundle_witness {frame : Frame} {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    prepareBundle frame files maximumBytes limits maximumPredicates maximumLiterals = .ok output.prepared ∧
      decodeV8 proof = .ok output.certificate ∧ WellFormed output.prepared output.certificate = true ∧
      retain output.prepared.problem output.certificate = .ok output.clauses := by
  cases preparedRun : prepareBundle frame files maximumBytes limits maximumPredicates maximumLiterals with
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

theorem buildBundle_check {frame : Frame} {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    Fang.Equality.Ordered.check output.prepared.problem output.certificate = .ok () := by
  rw [← retain_erases, (buildBundle_witness success).2.2.2]
  rfl

/-- A successful build is an accepted bundle pair for the same frame (the forward direction only). -/
theorem buildBundle_accepts {frame : Frame} {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    acceptsBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok () := by
  obtain ⟨preparedRun, decoded, wellFormed, _⟩ := buildBundle_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  simp [acceptsBundle, checkProblem, preparedRun, decoded, wellFormed, buildBundle_check success,
    Except.mapError, Bind.bind, Except.bind]

theorem buildBundle_refuted {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    BundleRefuted frame files maximumBytes bundleFuel :=
  acceptsBundle_refuted frameSound (buildBundle_accepts success)

theorem buildBundle_rows {frame : Frame} {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    Derivation.Checked output.prepared.problem [] (rows output) ∧
      (rows output).map Prod.snd = output.clauses := by
  obtain ⟨checkedSteps, _, _, _⟩ := retain_witness (buildBundle_witness success).2.2.2
  obtain ⟨values, checked, sameSteps, sameClauses⟩ := Derivation.checkSteps_rows checkedSteps
  simp only [List.nil_append] at sameClauses
  have paired : rows output = values := by
    rw [rows, ← sameSteps, ← sameClauses, Derivation.zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameClauses⟩

theorem buildBundle_row_checked {frame : Frame} {files maximumBytes proof limits maximumPredicates maximumLiterals
    output}
    (success : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : rows output = leading ++ value :: rest) :
    Fang.Equality.Ordered.checkStep output.prepared.problem (leading.map Prod.snd) value.1 = .ok value.2 := by
  have checked := (buildBundle_rows success).1
  rw [position] at checked
  simpa using checked.row

/-- What the source rows restate, for the frame of the build. -/
theorem buildBundle_sources {frame : Frame} {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    ∃ bundle items input, frame files maximumBytes = .ok bundle ∧
      Coverage.FramerV2.wellShaped bundle bundleFuel = true ∧ expand bundle bundleFuel = .ok items ∧
      readInput (declarationsOf bundle items) = some input ∧
      output.prepared.original = withGenerated input
        (Coverage.distinctAxioms input.predicates.length (objectIds input (declarationsOf bundle items))) := by
  obtain ⟨numeric, numericRun, replayRun⟩ := bind_success (buildBundle_witness success).1
  obtain ⟨bundle, items, input, framed, shaped, expanded, encoded, same⟩ :=
    bundleNumeric_witness (mapError_success numericRun)
  obtain ⟨_, _, _, _, original, _⟩ := replayFrom_witness (mapError_success replayRun)
  exact ⟨bundle, items, input, framed, shaped, expanded, encoded, original.trans same⟩

/-- Every model of the bundle under a sound frame, distinct objects separated, gives a model of the
    prepared problem. -/
theorem prepareBundle_models {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepareBundle frame files maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (satisfiable : ByteBundleSatisfiable frame files maximumBytes bundleFuel) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  obtain ⟨numeric, numericRun, replayRun⟩ := bind_success success
  have numericOk := mapError_success numericRun
  have numericSatisfiable : numeric.Satisfiable :=
    Classical.byContradiction fun refuted => bundleNumeric_unsat frameSound numericOk refuted satisfiable
  exact replayFrom_models (bundleNumeric_below frameSound numericOk) (mapError_success replayRun) numericSatisfiable

/-- SAP for the group of a built bundle pair under attached names, for a sound frame. -/
theorem bundle_group_sap {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals output}
    (success : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
    {stem functions names} (named : attachBundle output stem functions = .ok names)
    {formula} (formulaRun : Group.groupFormula names output.prepared.problem = .ok formula)
    (satisfiable : ByteBundleSatisfiable frame files maximumBytes bundleFuel) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨preparedRun, _, wellFormed, _⟩ := buildBundle_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  obtain ⟨D, nonempty, model, holds⟩ := prepareBundle_models frameSound preparedRun satisfiable
  have named' := namedModel_models (prepared := legacyPrepared output.prepared) (attachBundle_spec named)
    wellFormed.1 model holds
  exact ⟨D, nonempty, namedModel names model,
    ((Group.groupFormula_spec formulaRun).2.2 (namedModel names model)).mpr named'⟩

/-! The document: `BundleDocument` with the frame as a parameter. -/

/-- The document for a built pair. The bundle is framed again with the same frame. -/
def bundleDocumentOf (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat) (output : Output)
    (stem : String) (functions : List Frontend.Symbol) (groupLabel : String) (labels : List String) :
    Except String String :=
  match frame files maximumBytes with
  | .error _ => .error "export-error: the bundle does not frame"
  | .ok bundle =>
    match expand bundle bundleFuel with
    | .error _ => .error "export-error: the bundle does not expand"
    | .ok items =>
      if decide (documentNames ((declarationsOf bundle items).map Declaration.name) groupLabel labels).Nodup then
        bundleAssemble output bundle items stem functions groupLabel labels
      else .error "export-error: document names are not distinct"

theorem bundleDocumentOf_revision_two (files : List (Key × List UInt8)) (maximumBytes : Nat) (output : Output)
    (stem : String) (functions : List Frontend.Symbol) (groupLabel : String) (labels : List String) :
    bundleDocumentOf Coverage.FramerV2.frameBundle files maximumBytes output stem functions groupLabel labels =
      Bundle.bundleDocumentOf files maximumBytes output stem functions groupLabel labels := by
  unfold bundleDocumentOf Bundle.bundleDocumentOf
  rw [Coverage.FramerV2.frameBundleFast_eq]
  -- The two definitions use distinct auxiliary match functions with equal bodies.
  rfl

def bundleDocument (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) (stem : String)
    (functions : List Frontend.Symbol) (groupLabel : String) (labels : List String) : Except String String :=
  match buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these files"
  | .ok output => bundleDocumentOf frame files maximumBytes output stem functions groupLabel labels

structure BundleDocumentFacts (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat)
    (proof : String) (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) (stem : String)
    (functions : List Frontend.Symbol) (groupLabel : String) (labels : List String) (text : String) : Prop where
  facts : ∃ output bundle items names sources parents group rowTexts,
    buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
    acceptsBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok () ∧
    frame files maximumBytes = .ok bundle ∧
    Coverage.FramerV2.wellShaped bundle bundleFuel = true ∧
    expand bundle bundleFuel = .ok items ∧
    attachBundle output stem functions = .ok names ∧
    (bundle.map pathOf).Nodup ∧
    RowsFrame (items.filterMap (sourceItem bundle)) sources ∧
    ((declarationsOf bundle items).map Declaration.name).mapM parentText = .ok parents ∧
    sapRow names output.prepared.problem groupLabel parents = .ok group ∧
    Rows.render names groupLabel labels (rows output) = .ok rowTexts ∧
    (documentNames ((declarationsOf bundle items).map Declaration.name) groupLabel labels).Nodup ∧
    text = String.join (sources.map fun row => row.2 ++ "\n") ++ group ++ String.join rowTexts ∧
    text.utf8ByteSize ≤ maximumDocumentBytes

theorem bundleDocumentOf_spec {frame : Frame} {files maximumBytes proof limits maximumPredicates maximumLiterals
    output stem functions groupLabel labels text}
    (built : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
    (success : bundleDocumentOf frame files maximumBytes output stem functions groupLabel labels = .ok text) :
    BundleDocumentFacts frame files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels text := by
  obtain ⟨bundle', items', input, framed', shaped', expanded', _, _⟩ := buildBundle_sources built
  unfold bundleDocumentOf at success
  rw [framed'] at success
  simp only [expanded'] at success
  by_cases distinct : (documentNames ((declarationsOf bundle' items').map Declaration.name) groupLabel labels).Nodup
  · simp only [distinct, decide_true, ↓reduceIte] at success
    unfold bundleAssemble at success
    obtain ⟨names, namesRun, success⟩ := bind_success success
    obtain ⟨sources, sourcesRun, success⟩ := bind_success success
    obtain ⟨parents, parentsRun, success⟩ := bind_success success
    obtain ⟨group, groupRun, success⟩ := bind_success success
    obtain ⟨rowTexts, rowsRun, success⟩ := bind_success success
    obtain ⟨same, capped⟩ := capText_ok success
    obtain ⟨paths, framedRows⟩ := bundleSourceRows_spec sourcesRun
    exact ⟨⟨output, bundle', items', names, sources, parents, group, rowTexts, built, buildBundle_accepts built,
      framed', shaped', expanded', namesRun, paths, framedRows, parentsRun, groupRun, rowsRun, distinct,
      same, same ▸ capped⟩⟩
  · simp [distinct] at success

theorem bundleDocument_spec {frame : Frame} {files maximumBytes proof limits maximumPredicates maximumLiterals stem
    functions groupLabel labels text}
    (success : bundleDocument frame files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels = .ok text) :
    BundleDocumentFacts frame files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels text := by
  cases built : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals with
  | error reason => simp [bundleDocument, built] at success
  | ok output =>
    simp only [bundleDocument, built] at success
    exact bundleDocumentOf_spec built success

/-- A printed bundle document certifies the bundle refuted under a sound frame. -/
theorem bundleDocument_refuted {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals stem functions groupLabel labels text}
    (success : bundleDocument frame files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels = .ok text) :
    BundleRefuted frame files maximumBytes bundleFuel := by
  obtain ⟨⟨output, _, _, _, _, _, _, _, built, _⟩⟩ := bundleDocument_spec success
  exact buildBundle_refuted frameSound built

/-- The group row of a printed bundle document through `document_group`, with SAP against the meaning
    of the frame. -/
theorem bundleDocument_group_sap {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals stem functions groupLabel labels text}
    (success : bundleDocument frame files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels = .ok text) :
    ∃ output bundle items names parents group quoted body formula,
      buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      frame files maximumBytes = .ok bundle ∧
      expand bundle bundleFuel = .ok items ∧
      attachBundle output stem functions = .ok names ∧
      ((declarationsOf bundle items).map Declaration.name).mapM parentText = .ok parents ∧
      sapRow names output.prepared.problem groupLabel parents = .ok group ∧
      group = groupRowText quoted body (groupAnnotation parents) ∧
      QuotedAtom quoted.toList groupLabel.toList ∧
      Group.groupFormula names output.prepared.problem = .ok formula ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧ formula.Within [] ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      (∀ {D : Type} (model : Source.Interpretation D),
        (∀ valuation, formula.Holds model valuation) ↔
          Fang.Equality.models (tableModel names.view model) output.prepared.problem) ∧
      DataText (groupAnnotation parents) (sapDatum ((declarationsOf bundle items).map Declaration.name)) ∧
      (ByteBundleSatisfiable frame files maximumBytes bundleFuel →
        ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          ∀ valuation, formula.Holds model valuation) := by
  obtain ⟨⟨output, bundle, items, names, _, parents, group, _, built, _, framed, _, expanded, namesRun, _, _,
    parentsRun, groupRun, _⟩⟩ := bundleDocument_spec success
  obtain ⟨quoted, body, formula, printed, quotedLabel, formulaRun, parsed, closed, unique, meaning, annotation⟩ :=
    document_group parentsRun groupRun
  exact ⟨output, bundle, items, names, parents, group, quoted, body, formula, built, framed, expanded, namesRun,
    parentsRun, groupRun, printed, quotedLabel, formulaRun, parsed, closed, unique, meaning, annotation,
    fun satisfiable => bundle_group_sap frameSound built namesRun formulaRun satisfiable⟩

/-- SAP against the printed source rows, in the shape of the single-file `document_rows_sap`. -/
theorem bundleDocument_rows_sap {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals stem functions groupLabel labels text}
    (success : bundleDocument frame files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels = .ok text) :
    ∃ output bundle items names sources parents group rowTexts formula,
      buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      frame files maximumBytes = .ok bundle ∧
      expand bundle bundleFuel = .ok items ∧
      attachBundle output stem functions = .ok names ∧
      RowsFrame (items.filterMap (sourceItem bundle)) sources ∧
      ((declarationsOf bundle items).map Declaration.name).mapM parentText = .ok parents ∧
      sapRow names output.prepared.problem groupLabel parents = .ok group ∧
      text = String.join (sources.map fun row => row.2 ++ "\n") ++ group ++ String.join rowTexts ∧
      Group.groupFormula names output.prepared.problem = .ok formula ∧
      ∀ read : List Declaration,
        Paired (fun row value => Coverage.FramerV2.frameFile (rowBytes row.2) maximumRowBytes =
          .ok [.formula value]) sources read →
        (∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          Fang.TptpCandidate.FullFof.Models (source read) model ∧
          Coverage.FramerV2.NamedSeparated model (Coverage.FramerV2.objectNames read)) →
        ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          ∀ valuation, formula.Holds model valuation := by
  obtain ⟨⟨output, bundle, items, names, sources, parents, group, rowTexts, built, _, framed, shaped, expanded,
    namesRun, _, framedRows, parentsRun, groupRun, _, _, same, _⟩⟩ := bundleDocument_spec success
  obtain ⟨_, _, formula, _, _, formulaRun, _⟩ := document_group parentsRun groupRun
  refine ⟨output, bundle, items, names, sources, parents, group, rowTexts, formula, built, framed, expanded,
    namesRun, framedRows, parentsRun, groupRun, same, formulaRun, ?_⟩
  intro read reading model
  have bodies := rows_read_bodies framedRows reading
  have declarations : (items.filterMap (sourceItem bundle)).map (Declaration.body ∘ Prod.snd) =
      (declarationsOf bundle items).map Declaration.body := by
    rw [← sourceItems_declarations bundle items, List.map_map]
  have sameSource : source read = source (declarationsOf bundle items) :=
    source_of_bodies (bodies.trans declarations)
  obtain ⟨D, nonempty, interpretation, models, separated⟩ := model
  have satisfiable : ByteBundleSatisfiable frame files maximumBytes bundleFuel := by
    refine ⟨bundle, items, framed, shaped, expanded, D, nonempty, interpretation, ?_, ?_⟩
    · rw [← sameSource]
      exact models
    · simpa [Coverage.FramerV2.objectNames, sameSource] using separated
  exact bundle_group_sap frameSound built namesRun formulaRun satisfiable

/-! Product entry: generated names. -/

/-- The product entry for a frame: generated names, then the same checks as `bundleDocument`. -/
def exportBundleDocument (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) : Except String String :=
  match buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these files"
  | .ok output =>
    bundleDocumentOf frame files maximumBytes output (objectStem output)
      (bundleExportFunctions output (objectStem output)) (exportLabels output).1 (exportLabels output).2

theorem exportBundleDocument_revision_two (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    exportBundleDocument Coverage.FramerV2.frameBundle files maximumBytes proof limits maximumPredicates
      maximumLiterals = Bundle.exportBundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals := by
  unfold exportBundleDocument Bundle.exportBundleDocument
  rw [buildBundle_revision_two]
  cases Bundle.buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals with
  | error reason => rfl
  | ok output => exact bundleDocumentOf_revision_two _ _ _ _ _ _ _

theorem exportBundleDocument_spec {frame : Frame} {files maximumBytes proof limits maximumPredicates maximumLiterals
    text}
    (success : exportBundleDocument frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok text) :
    ∃ output, buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      bundleDocument frame files maximumBytes proof limits maximumPredicates maximumLiterals (objectStem output)
        (bundleExportFunctions output (objectStem output)) (exportLabels output).1 (exportLabels output).2 =
          .ok text := by
  cases built : buildBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals with
  | error reason => simp [exportBundleDocument, built] at success
  | ok output =>
    simp only [exportBundleDocument, built] at success
    exact ⟨output, rfl, by simp only [bundleDocument, built]; exact success⟩

theorem exportBundleDocument_refuted {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals text}
    (success : exportBundleDocument frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok text) :
    BundleRefuted frame files maximumBytes bundleFuel := by
  obtain ⟨_, _, document⟩ := exportBundleDocument_spec success
  exact bundleDocument_refuted frameSound document

/-- A document exported with the hashed framer at any limit refutes the bundle under the list framer
    with that limit. -/
theorem exportBundleDocument_hashed_refuted (limit : Nat)
    {files maximumBytes proof limits maximumPredicates maximumLiterals text}
    (success : exportBundleDocument (frameBundleHashed limit) files maximumBytes proof limits maximumPredicates
      maximumLiterals = .ok text) :
    BundleRefuted (frameBundle limit) files maximumBytes bundleFuel := by
  rw [Coverage.FramerLimit.frameBundleHashed_eq] at success
  exact exportBundleDocument_refuted (Coverage.FramerLimit.frameBundle_sound limit) success

/-- At 1,000 formulas per file the hashed entry is the entry of the earlier exporter. -/
theorem exportBundleDocument_hashed_accepted (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    exportBundleDocument (frameBundleHashed 1000) files maximumBytes proof limits maximumPredicates maximumLiterals =
      Bundle.exportBundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals := by
  rw [Coverage.FramerLimit.frameBundleHashed_accepted, exportBundleDocument_revision_two]

#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.buildBundle_revision_two
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.buildBundle_witness
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.buildBundle_check
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.buildBundle_accepts
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.buildBundle_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.buildBundle_rows
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.buildBundle_row_checked
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.buildBundle_sources
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.prepareBundle_models
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.bundle_group_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.bundleDocumentOf_revision_two
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.bundleDocumentOf_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.bundleDocument_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.bundleDocument_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.bundleDocument_group_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.bundleDocument_rows_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument_revision_two
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument_hashed_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument_hashed_accepted

end Fang.QuantifiedEqualityTstp.Expanded.BundleLimit
