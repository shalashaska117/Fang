/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The TSTP refutation document of a sealed bundle: one source row per
   expanded declaration with the path of its file, one SAP group row naming
   every source declaration, then the annotated clause rows. The group and the
   clause rows are the single-file document's, printed from the prepared
   problem of the bundle pair under names checked against the original tables
   with distinct objects renamed; the generated distinct-object clauses appear
   only inside the group. SAP is stated against the revision-2 bundle meaning
   and against the framer's reading of the printed source rows. -/
import ExpandedDocument
import BundleTrace
import BundleSourceRow

namespace Fang.QuantifiedEqualityTstp.Expanded.Bundle

open Aeneas.Std
open Fang.TptpCandidate Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration TstpText
open Fang.TptpCandidate.FullFof.Coverage (Key Item Bundle expand declarationsOf)
open Fang.TptpCandidate.FullFof.Coverage.BundleV8
open Fang.QuantifiedEqualityTstp.Expanded

theorem bind_success {α β : Type} {action : Except String α} {next : α → Except String β} {result : β}
    (success : action >>= next = .ok result) : ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error reason => cases success
  | ok value => exact ⟨value, rfl, success⟩

/-- The body of the document for a framed and expanded bundle. -/
def bundleAssemble (output : Output) (bundle : Bundle) (items : List Item) (stem : String)
    (functions : List Frontend.Symbol) (groupLabel : String) (labels : List String) : Except String String := do
  let names ← attachBundle output stem functions
  let sources ← bundleSourceRows bundle items
  let parents ← ((declarationsOf bundle items).map Declaration.name).mapM parentText
  let group ← sapRow names output.prepared.problem groupLabel parents
  let rowTexts ← Rows.render names groupLabel labels (rows output)
  capText (String.join (sources.map fun row => row.2 ++ "\n") ++ group ++ String.join rowTexts)

/-- The document for a built pair. The bundle is framed and expanded again,
    with the linear framer; after a successful build both steps succeed. -/
def bundleDocumentOf (files : List (Key × List UInt8)) (maximumBytes : Nat) (output : Output) (stem : String)
    (functions : List Frontend.Symbol) (groupLabel : String) (labels : List String) : Except String String :=
  match Coverage.FramerV2.frameBundleFast files maximumBytes with
  | .error _ => .error "export-error: the bundle does not frame"
  | .ok bundle =>
    match expand bundle bundleFuel with
    | .error _ => .error "export-error: the bundle does not expand"
    | .ok items =>
      if decide (documentNames ((declarationsOf bundle items).map Declaration.name) groupLabel labels).Nodup then
        bundleAssemble output bundle items stem functions groupLabel labels
      else .error "export-error: document names are not distinct"

def bundleDocument (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) (stem : String)
    (functions : List Frontend.Symbol) (groupLabel : String) (labels : List String) : Except String String :=
  match buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these files"
  | .ok output => bundleDocumentOf files maximumBytes output stem functions groupLabel labels

structure BundleDocumentFacts (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) (stem : String)
    (functions : List Frontend.Symbol) (groupLabel : String) (labels : List String) (text : String) : Prop where
  facts : ∃ output bundle items names sources parents group rowTexts,
    buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
    acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok () ∧
    Coverage.FramerV2.frameBundle files maximumBytes = .ok bundle ∧
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

theorem bundleDocumentOf_spec {files maximumBytes proof limits maximumPredicates maximumLiterals output stem
    functions groupLabel labels text}
    (built : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
    (success : bundleDocumentOf files maximumBytes output stem functions groupLabel labels = .ok text) :
    BundleDocumentFacts files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels text := by
  obtain ⟨bundle', items', input, framed', shaped', expanded', _, _⟩ := buildBundle_sources built
  unfold bundleDocumentOf at success
  rw [Coverage.FramerV2.frameBundleFast_eq, framed'] at success
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

theorem bundleDocument_spec {files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
    groupLabel labels text}
    (success : bundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels = .ok text) :
    BundleDocumentFacts files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels text := by
  cases built : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals with
  | error reason => simp [bundleDocument, built] at success
  | ok output =>
    simp only [bundleDocument, built] at success
    exact bundleDocumentOf_spec built success

/-- A printed bundle document certifies the sealed bundle refuted. -/
theorem bundleDocument_refuted {files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
    groupLabel labels text}
    (success : bundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels = .ok text) :
    BundleRefuted files maximumBytes bundleFuel := by
  obtain ⟨⟨output, _, _, _, _, _, _, _, built, _⟩⟩ := bundleDocument_spec success
  exact buildBundle_refuted built

/-- The group row of a printed bundle document, through `document_group`:
    its parents are the source declaration names, its reading is unique and
    closed and holds in a source model exactly when the prepared problem holds
    in the table model, its annotation reads as `status(sap)` over the source
    names, and that reading holds in some source model whenever the sealed
    bundle has a model in which different distinct objects denote different
    elements. -/
theorem bundleDocument_group_sap {files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
    groupLabel labels text}
    (success : bundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels = .ok text) :
    ∃ output bundle items names parents group quoted body formula,
      buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      Coverage.FramerV2.frameBundle files maximumBytes = .ok bundle ∧
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
      (Coverage.FramerV2.ByteBundleSatisfiable files maximumBytes bundleFuel →
        ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          ∀ valuation, formula.Holds model valuation) := by
  obtain ⟨⟨output, bundle, items, names, _, parents, group, _, built, _, framed, _, expanded, namesRun, _, _,
    parentsRun, groupRun, _⟩⟩ := bundleDocument_spec success
  obtain ⟨quoted, body, formula, printed, quotedLabel, formulaRun, parsed, closed, unique, meaning, annotation⟩ :=
    document_group parentsRun groupRun
  exact ⟨output, bundle, items, names, parents, group, quoted, body, formula, built, framed, expanded, namesRun,
    parentsRun, groupRun, printed, quotedLabel, formulaRun, parsed, closed, unique, meaning, annotation,
    fun satisfiable => bundle_group_sap built namesRun formulaRun satisfiable⟩

theorem source_of_bodies {read values : List Declaration}
    (same : read.map Declaration.body = values.map Declaration.body) : source read = source values := by
  have left : source read = (read.map Declaration.body).map Body.formula := by simp [source]
  have right : source values = (values.map Declaration.body).map Body.formula := by simp [source]
  rw [left, right, same]

/-- SAP against the printed source rows, in the shape of the single-file
    `document_rows_sap`: for the declarations the framer reads from the
    printed rows, in order, a model of them in which different distinct
    objects denote different elements makes the group formula hold in some
    source model. -/
theorem bundleDocument_rows_sap {files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
    groupLabel labels text}
    (success : bundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals stem functions
      groupLabel labels = .ok text) :
    ∃ output bundle items names sources parents group rowTexts formula,
      buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      Coverage.FramerV2.frameBundle files maximumBytes = .ok bundle ∧
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
  have satisfiable : Coverage.FramerV2.ByteBundleSatisfiable files maximumBytes bundleFuel := by
    refine ⟨bundle, items, framed, shaped, expanded, D, nonempty, interpretation, ?_, ?_⟩
    · rw [← sameSource]
      exact models
    · simpa [Coverage.FramerV2.objectNames, sameSource] using separated
  exact bundle_group_sap built namesRun formulaRun satisfiable

/-! ### Product entry: generated names -/

/-- The stem for renamed distinct objects, a prefix of no original name. -/
def objectStem (output : Output) : String :=
  freshPrefix (Naming.originalNames output.prepared.original.functions output.prepared.original.predicates)
    "fang_object" "_"

/-- The renamed original table, then fresh names for the symbols added by preprocessing. -/
def bundleExportFunctions (output : Output) (stem : String) : List Frontend.Symbol :=
  let original := output.prepared.original
  let renamed := renameObjects stem original.functions
  let skolem := freshPrefix (Naming.originalNames renamed original.predicates) "sk" "f"
  Naming.symbols renamed ++
    (output.prepared.functionArities.drop original.functions.length).mapIdx
      fun index arity => ⟨skolem ++ toString index, some arity⟩

/-- The product entry: the linear framer, generated names, then the same checks as `bundleDocument`. -/
def exportBundleDocument (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) : Except String String :=
  match buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these files"
  | .ok output =>
    bundleDocumentOf files maximumBytes output (objectStem output) (bundleExportFunctions output (objectStem output))
      (exportLabels output).1 (exportLabels output).2

theorem exportBundleDocument_spec {files maximumBytes proof limits maximumPredicates maximumLiterals text}
    (success : exportBundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals = .ok text) :
    ∃ output, buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output ∧
      bundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals (objectStem output)
        (bundleExportFunctions output (objectStem output)) (exportLabels output).1 (exportLabels output).2 = .ok text := by
  cases built : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals with
  | error reason => simp [exportBundleDocument, built] at success
  | ok output =>
    simp only [exportBundleDocument, built] at success
    exact ⟨output, rfl, by simp only [bundleDocument, built]; exact success⟩

theorem exportBundleDocument_refuted {files maximumBytes proof limits maximumPredicates maximumLiterals text}
    (success : exportBundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals = .ok text) :
    BundleRefuted files maximumBytes bundleFuel := by
  obtain ⟨_, _, document⟩ := exportBundleDocument_spec success
  exact bundleDocument_refuted document

#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bind_success
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bundleDocumentOf_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bundleDocument_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bundleDocument_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bundleDocument_group_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.source_of_bodies
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bundleDocument_rows_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.exportBundleDocument_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.exportBundleDocument_refuted

end Fang.QuantifiedEqualityTstp.Expanded.Bundle
