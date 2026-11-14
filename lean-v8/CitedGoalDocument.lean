import CitedModels

namespace Fang.TptpCandidate.CitedDocument
open FullFof Roles.Bundle Roles.Bundle.V3 Roles.Bundle.V3.Depth
open Fang.QuantifiedEqualityTstp Fang.TstpText
open FangQuantifiedEqualityReplay (bind_success mapError_success)

def goalFormula (entry : Roles.Bytes.Entry) : Except String Formula :=
  if entry.role = .conjecture then
    match entry.original.body with
    | .fof formula => .ok formula
    | _ => .error "export-error: selected conjecture is not FOF"
  else .error "export-error: selected item is not a conjecture"

theorem goalFormula_spec {entry formula} (success : goalFormula entry = .ok formula) :
    entry.role = .conjecture ∧ entry.original.body = .fof formula := by
  unfold goalFormula at success
  split at success
  · rename_i role
    split at success
    · rename_i value body
      cases success
      exact ⟨role, body⟩
    · cases success
  · cases success

def groupParents (values : List Roles.Bytes.Entry) (negatedLabel : String) : List Name :=
  (GoalRows.premiseEntries values).map (fun entry => entry.original.name) ++ [.atom negatedLabel]

theorem groupParents_semantics (values : List Roles.Bytes.Entry) (negatedLabel : String) :
    groupParents values negatedLabel =
      (Roles.premises (Roles.Bytes.source values)).map Roles.Declaration.metadata ++ [.atom negatedLabel] := by
  rw [groupParents, GoalDocument.NamedDepth.premiseEntries_names]

def goalDocumentOf (maxDepth : Nat) (output : Output) (read : BundleRead) (cited : List Coverage.Item)
    (entry : Roles.Bytes.Entry) (formula : Formula) (proposed : Body.Names)
    (negatedLabel groupLabel : String) (labels : List String) : Except String String := do
  let kept := keptItems read.items cited (some output.prepared.item)
  let values := entriesOf read.bundle kept
  let names ← attachNames output.prepared.replay proposed
  if (GoalRows.goalNames (values.map (fun entry => entry.original.name)) negatedLabel groupLabel labels).Nodup then
    let sources ← SourceRows.sourceRows maxDepth read.bundle kept
    let negated ← SourceRows.negatedRow maxDepth negatedLabel entry.original.name formula
    let parents ← (groupParents values negatedLabel).mapM Expanded.parentText
    let group ← Expanded.sapRow names output.prepared.replay.problem groupLabel parents
    let rows ← Rows.render names groupLabel labels (Expanded.rows (expandedOutput output))
    Expanded.capText (String.join (sources.map (fun row => row.2 ++ "\n")) ++ negated ++ "\n" ++ group ++ String.join rows)
  else .error "export-error: document names are not distinct"

def goalDocument (frame : Frame) (maxDepth : Nat) (files : List (Coverage.Key × List UInt8))
    (maximumBytes index : Nat) (cited : List Coverage.Item) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize)
    (proposed : Body.Names) (negatedLabel groupLabel : String) (labels : List String) : Except String String := do
  let output ← (build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals).mapError
    (fun _ => "export-error: the cited goal task is not accepted")
  let read ← (readBundle frame files maximumBytes).mapError (fun _ => "export-error: source bundle does not decode")
  let some source := SourceRows.sourceItem read.bundle output.prepared.item
    | .error "export-error: original goal item is missing"
  let formula ← goalFormula source.2
  goalDocumentOf maxDepth output read cited source.2 formula proposed negatedLabel groupLabel labels

theorem goalDocument_spec {frame maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
    proposed negatedLabel groupLabel labels text}
    (success : goalDocument frame maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
      proposed negatedLabel groupLabel labels = .ok text) :
    ∃ output read source formula names sources negated parents group rows,
      build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      readBundle frame files maximumBytes = .ok read ∧
      SourceRows.sourceItem read.bundle output.prepared.item = some source ∧
      goalFormula source.2 = .ok formula ∧
      attachNames output.prepared.replay proposed = .ok names ∧
      (GoalRows.goalNames ((entriesOf read.bundle (keptItems read.items cited (some output.prepared.item))).map
        (fun entry => entry.original.name)) negatedLabel groupLabel labels).Nodup ∧
      SourceRows.sourceRows maxDepth read.bundle (keptItems read.items cited (some output.prepared.item)) = .ok sources ∧
      SourceRows.negatedRow maxDepth negatedLabel source.2.original.name formula = .ok negated ∧
      (groupParents (entriesOf read.bundle (keptItems read.items cited (some output.prepared.item))) negatedLabel).mapM
        Expanded.parentText = .ok parents ∧
      Expanded.sapRow names output.prepared.replay.problem groupLabel parents = .ok group ∧
      Rows.render names groupLabel labels (Expanded.rows (expandedOutput output)) = .ok rows ∧
      text = String.join (sources.map (fun row => row.2 ++ "\n")) ++ negated ++ "\n" ++ group ++ String.join rows ∧
      text.utf8ByteSize ≤ Expanded.maximumDocumentBytes := by
  unfold goalDocument at success
  obtain ⟨output, built, success⟩ := bind_success success
  obtain ⟨read, readRun, success⟩ := bind_success success
  split at success
  · rename_i source sourceAt
    obtain ⟨formula, formulaRun, success⟩ := bind_success success
    unfold goalDocumentOf at success
    obtain ⟨names, named, success⟩ := bind_success success
    split at success
    · rename_i distinct
      obtain ⟨sources, sourcesRun, success⟩ := bind_success success
      obtain ⟨negated, negatedRun, success⟩ := bind_success success
      obtain ⟨parents, parentsRun, success⟩ := bind_success success
      obtain ⟨group, groupRun, success⟩ := bind_success success
      obtain ⟨rows, rowsRun, success⟩ := bind_success success
      obtain ⟨same, capped⟩ := Expanded.capText_ok success
      subst same
      exact ⟨output, read, source, formula, names, sources, negated, parents, group, rows,
        mapError_success built, mapError_success readRun, sourceAt, formulaRun, named, distinct,
        sourcesRun, negatedRun, parentsRun, groupRun, rowsRun, rfl, capped⟩
    · cases success
  · cases success

theorem goalDocument_checked {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
      proposed negatedLabel groupLabel labels text}
    (success : goalDocument frame maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
      proposed negatedLabel groupLabel labels = .ok text) :
    ∃ (output : Output) (read : BundleRead), ∃ names sources rows,
      GoalEntailed frame files maximumBytes bundleFuel output.prepared.item ∧
      SourceRows.RowsRead maxDepth
        ((keptItems read.items cited (some output.prepared.item)).filterMap (SourceRows.sourceItem read.bundle)) sources ∧
      Derivation.Checked output.prepared.replay.problem [] (Expanded.rows (expandedOutput output)) ∧
      Source.RelatedLists (fun pair row => Rows.RowCorrespondence names groupLabel labels pair.1 pair.2 row)
        (labels.zip (Expanded.rows (expandedOutput output))) rows ∧
      ((Expanded.rows (expandedOutput output))[output.certificate.final]?).map Prod.snd = some [] ∧
      text.utf8ByteSize ≤ Expanded.maximumDocumentBytes := by
  obtain ⟨output, read, _, _, names, sources, _, _, _, rows, built, _, _, _, _, _, sourcesRun, _, _, _, rowsRun, _, capped⟩ :=
    goalDocument_spec success
  exact ⟨output, read, names, sources, rows, build_entails frameSound built,
    (SourceRows.sourceRows_spec sourcesRun).2, (rows_checked built).1, (Rows.render_correspondence rowsRun).2,
    (final_row_empty built).1, capped⟩

theorem goalDocument_group {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
      proposed negatedLabel groupLabel labels text}
    (success : goalDocument frame maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
      proposed negatedLabel groupLabel labels = .ok text) :
    ∃ (output : Output) (read : BundleRead), ∃ names parents group quoted body formula,
      Expanded.sapRow names output.prepared.replay.problem groupLabel parents = .ok group ∧
      group = Expanded.groupRowText quoted body (Expanded.groupAnnotation parents) ∧
      DataText (Expanded.groupAnnotation parents)
        (Expanded.sapDatum ((Roles.premises (Roles.Bytes.source
          (entriesOf read.bundle (keptItems read.items cited (some output.prepared.item))))).map
            Roles.Declaration.metadata ++ [.atom negatedLabel])) ∧
      Group.groupFormula names output.prepared.replay.problem = .ok formula ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      formula.Within [] ∧
      (∀ {D : Type} (model : Source.Interpretation D), (∀ valuation, formula.Holds model valuation) ↔
        Fang.Equality.models (tableModel names.view model) output.prepared.replay.problem) ∧
      (GoalCountermodel frame files maximumBytes cited output.prepared.item →
        ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D), ∀ valuation, formula.Holds model valuation) := by
  obtain ⟨output, read, _, _, names, _, _, parents, group, _, built, _, _, _, named, _, _, _, parentsRun, groupRun, _, _, _⟩ :=
    goalDocument_spec success
  have printed := groupRun
  unfold Expanded.sapRow at printed
  obtain ⟨quoted, _, printed⟩ := bind_success printed
  obtain ⟨body, bodyRun, printed⟩ := bind_success printed
  obtain ⟨formula, formulaRun, parsed, _, unique, _⟩ := Group.groupText_spec bodyRun
  have annotation := Expanded.sap_annotation parentsRun
  rw [groupParents_semantics] at annotation
  exact ⟨output, read, names, parents, group, quoted, body, formula, groupRun, (Except.ok.inj printed).symm, annotation,
    formulaRun, parsed, unique, (Group.groupFormula_spec formulaRun).2.1, (Group.groupFormula_spec formulaRun).2.2,
    goal_group_sap frameSound built named formulaRun⟩

def exportGoalDocument (frame : Frame) (maxDepth : Nat) (files : List (Coverage.Key × List UInt8))
    (maximumBytes index : Nat) (cited : List Coverage.Item) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except String String := do
  let output ← (build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals).mapError
    (fun _ => "export-error: the cited goal task is not accepted")
  let read ← (readBundle frame files maximumBytes).mapError (fun _ => "export-error: source bundle does not decode")
  let values := entriesOf read.bundle (keptItems read.items cited (some output.prepared.item))
  let labels := GoalDocument.NamedDepth.goalLabels (GoalDocument.NamedDepth.atomNames values)
    (Expanded.rows (expandedOutput output)).length
  goalDocument frame maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
    (outputNames output.prepared.replay) labels.1 labels.2.1 labels.2.2

theorem exportGoalDocument_spec {frame maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals text}
    (success : exportGoalDocument frame maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok text) :
    ∃ proposed negatedLabel groupLabel labels,
      goalDocument frame maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
        proposed negatedLabel groupLabel labels = .ok text := by
  unfold exportGoalDocument at success
  obtain ⟨output, _, success⟩ := bind_success success
  obtain ⟨read, _, success⟩ := bind_success success
  exact ⟨_, _, _, _, success⟩

#print axioms goalFormula_spec
#print axioms goalDocument_spec
#print axioms goalDocument_checked
#print axioms goalDocument_group
#print axioms exportGoalDocument_spec
end Fang.TptpCandidate.CitedDocument
