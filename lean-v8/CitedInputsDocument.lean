import CitedInputsTrace

namespace Fang.TptpCandidate.CitedDocument.Inputs
open FullFof Roles.Bundle Roles.Bundle.V3 Roles.Bundle.V3.Depth
open Fang.QuantifiedEqualityTstp Fang.TstpText
open FangQuantifiedEqualityReplay (bind_success mapError_success)

def parentsOf (values : List Roles.Bytes.Entry) : List Name :=
  (Roles.positiveInputs (Roles.Bytes.source values)).map Roles.Declaration.metadata

def documentOf (maxDepth : Nat) (output : Output) (read : BundleRead) (cited : List Coverage.Item)
    (proposed : Body.Names) (groupLabel : String) (labels : List String) : Except String String := do
  let kept := keptItems read.items cited none
  let values := entriesOf read.bundle kept
  let names ← attachNames output.prepared proposed
  if ((values.map (fun entry => entry.original.name)) ++ .atom groupLabel :: labels.map Name.atom).Nodup then
    let sources ← SourceRows.sourceRows maxDepth read.bundle kept
    let parents ← (parentsOf values).mapM Expanded.parentText
    let group ← Expanded.sapRow names output.prepared.problem groupLabel parents
    let rows ← Rows.render names groupLabel labels (Expanded.rows (expandedOutput output))
    Expanded.capText (String.join (sources.map (fun row => row.2 ++ "\n")) ++ group ++ String.join rows)
  else .error "export-error: document names are not distinct"

def document (frame : Frame) (maxDepth : Nat) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (cited : List Coverage.Item) (proof : String) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize)
    (proposed : Body.Names) (groupLabel : String) (labels : List String) : Except String String := do
  let output ← (build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals).mapError
    (fun _ => "export-error: the cited inputs task is not accepted")
  let read ← (readBundle frame files maximumBytes).mapError (fun _ => "export-error: source bundle does not decode")
  documentOf maxDepth output read cited proposed groupLabel labels

theorem document_spec {frame maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals
    proposed groupLabel labels text}
    (success : document frame maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals
      proposed groupLabel labels = .ok text) :
    ∃ output read names sources parents group rows,
      build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      readBundle frame files maximumBytes = .ok read ∧
      attachNames output.prepared proposed = .ok names ∧
      (((entriesOf read.bundle (keptItems read.items cited none)).map (fun entry => entry.original.name)) ++
        .atom groupLabel :: labels.map Name.atom).Nodup ∧
      SourceRows.sourceRows maxDepth read.bundle (keptItems read.items cited none) = .ok sources ∧
      (parentsOf (entriesOf read.bundle (keptItems read.items cited none))).mapM Expanded.parentText = .ok parents ∧
      Expanded.sapRow names output.prepared.problem groupLabel parents = .ok group ∧
      Rows.render names groupLabel labels (Expanded.rows (expandedOutput output)) = .ok rows ∧
      text = String.join (sources.map (fun row => row.2 ++ "\n")) ++ group ++ String.join rows ∧
      text.utf8ByteSize ≤ Expanded.maximumDocumentBytes := by
  unfold document at success
  obtain ⟨output, built, success⟩ := bind_success success
  obtain ⟨read, decoded, success⟩ := bind_success success
  unfold documentOf at success
  obtain ⟨names, named, success⟩ := bind_success success
  split at success
  · rename_i distinct
    obtain ⟨sources, sourcesRun, success⟩ := bind_success success
    obtain ⟨parents, parentsRun, success⟩ := bind_success success
    obtain ⟨group, groupRun, success⟩ := bind_success success
    obtain ⟨rows, rowsRun, success⟩ := bind_success success
    obtain ⟨same, capped⟩ := Expanded.capText_ok success
    subst same
    exact ⟨output, read, names, sources, parents, group, rows, mapError_success built, mapError_success decoded,
      named, distinct, sourcesRun, parentsRun, groupRun, rowsRun, rfl, capped⟩
  · cases success

theorem document_checked {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals proposed groupLabel labels text}
    (success : document frame maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals
      proposed groupLabel labels = .ok text) :
    ByteUnsatisfiable frame files maximumBytes bundleFuel ∧
    ∃ (output : Output) (read : BundleRead), ∃ names sources rows,
      SourceRows.RowsRead maxDepth ((keptItems read.items cited none).filterMap (SourceRows.sourceItem read.bundle)) sources ∧
      Derivation.Checked output.prepared.problem [] (Expanded.rows (expandedOutput output)) ∧
      Source.RelatedLists (fun pair row => Rows.RowCorrespondence names groupLabel labels pair.1 pair.2 row)
        (labels.zip (Expanded.rows (expandedOutput output))) rows ∧
      ((Expanded.rows (expandedOutput output))[output.certificate.final]?).map Prod.snd = some [] ∧
      text.utf8ByteSize ≤ Expanded.maximumDocumentBytes := by
  obtain ⟨output, read, names, sources, _, _, rows, built, _, _, _, sourcesRun, _, _, rowsRun, _, capped⟩ := document_spec success
  exact ⟨build_unsat frameSound built, output, read, names, sources, rows,
    (SourceRows.sourceRows_spec sourcesRun).2, (rows_checked built).1, (Rows.render_correspondence rowsRun).2,
    (final_row_empty built).1, capped⟩

theorem document_group {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals proposed groupLabel labels text}
    (success : document frame maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals
      proposed groupLabel labels = .ok text) :
    ∃ (output : Output) (read : BundleRead), ∃ names parents group quoted body formula,
      Expanded.sapRow names output.prepared.problem groupLabel parents = .ok group ∧
      group = Expanded.groupRowText quoted body (Expanded.groupAnnotation parents) ∧
      DataText (Expanded.groupAnnotation parents) (Expanded.sapDatum (parentsOf (entriesOf read.bundle (keptItems read.items cited none)))) ∧
      Group.groupFormula names output.prepared.problem = .ok formula ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      formula.Within [] ∧
      (∀ {D : Type} (model : Source.Interpretation D), (∀ valuation, formula.Holds model valuation) ↔
        Fang.Equality.models (tableModel names.view model) output.prepared.problem) ∧
      (InputsModel frame files maximumBytes cited →
        ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D), ∀ valuation, formula.Holds model valuation) := by
  obtain ⟨output, read, names, _, parents, group, _, built, _, named, _, _, parentsRun, groupRun, _, _, _⟩ := document_spec success
  have printed := groupRun
  unfold Expanded.sapRow at printed
  obtain ⟨quoted, _, printed⟩ := bind_success printed
  obtain ⟨body, bodyRun, printed⟩ := bind_success printed
  obtain ⟨formula, formulaRun, parsed, _, unique, _⟩ := Group.groupText_spec bodyRun
  exact ⟨output, read, names, parents, group, quoted, body, formula, groupRun, (Except.ok.inj printed).symm,
    Expanded.sap_annotation parentsRun, formulaRun, parsed, unique, (Group.groupFormula_spec formulaRun).2.1,
    (Group.groupFormula_spec formulaRun).2.2, group_sap frameSound built named formulaRun⟩

def exportDocument (frame : Frame) (maxDepth : Nat) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (cited : List Coverage.Item) (proof : String) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except String String := do
  let output ← (build frame files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals).mapError
    (fun _ => "export-error: the cited inputs task is not accepted")
  let read ← (readBundle frame files maximumBytes).mapError (fun _ => "export-error: source bundle does not decode")
  let values := entriesOf read.bundle (keptItems read.items cited none)
  let labels := GoalDocument.NamedDepth.goalLabels (GoalDocument.NamedDepth.atomNames values) (Expanded.rows (expandedOutput output)).length
  document frame maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals
    (outputNames output.prepared) labels.2.1 labels.2.2

theorem exportDocument_spec {frame maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals text}
    (success : exportDocument frame maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals = .ok text) :
    ∃ proposed groupLabel labels, document frame maxDepth files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals
      proposed groupLabel labels = .ok text := by
  unfold exportDocument at success
  obtain ⟨output, _, success⟩ := bind_success success
  obtain ⟨read, _, success⟩ := bind_success success
  exact ⟨_, _, _, success⟩

#print axioms document_spec
#print axioms document_checked
#print axioms document_group
#print axioms exportDocument_spec
end Fang.TptpCandidate.CitedDocument.Inputs
