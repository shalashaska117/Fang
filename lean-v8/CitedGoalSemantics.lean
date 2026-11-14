import CitedGoalDocument

namespace Fang.TptpCandidate.CitedDocument
open FullFof Roles.Bundle Roles.Bundle.V3 Roles.Bundle.V3.Depth

theorem selected_goal_closed {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output read source formula}
    (built : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output)
    (decoded : readBundle frame files maximumBytes = .ok read)
    (sourceAt : SourceRows.sourceItem read.bundle output.prepared.item = some source)
    (formulaRun : goalFormula source.2 = .ok formula) :
    source.2 ∈ entriesOf read.bundle (keptItems read.items cited (some output.prepared.item)) ∧ formula.Within [] := by
  obtain ⟨actual, _, _, _, _, _, _, keptEntry, _, actualRun, _, _, located, _, _, _⟩ := source_task built
  have sameRead : actual = read := Except.ok.inj (actualRun.symm.trans decoded)
  subst actual
  have atGoal := V2.goalItems_entry (List.mem_of_getElem? located)
  rw [SourceRows.sourceItem_at sourceAt] at atGoal
  have sameEntry : keptEntry = source.2 := by simpa using atGoal.symm
  have member := (goalItems_member (List.mem_of_getElem? located)).1
  rw [sameEntry] at member
  obtain ⟨expanded, _, _⟩ := readBundle_witness decoded
  have closed := entries_closed (frameSound expanded.1) _ _ member
  rw [(goalFormula_spec formulaRun).2] at closed
  exact ⟨member, closed⟩

theorem selected_goal_negated {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output read source formula}
    (built : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output)
    (decoded : readBundle frame files maximumBytes = .ok read)
    (sourceAt : SourceRows.sourceItem read.bundle output.prepared.item = some source)
    (formulaRun : goalFormula source.2 = .ok formula)
    (D : Type) (inhabited : Nonempty D) (model : Source.Interpretation D) :
    (¬ Roles.Bytes.sentence model (entryDeclaration source.2).original) ↔
      Roles.Bytes.sentence model (.neg formula) := by
  let _ : Nonempty D := inhabited
  have closed := (selected_goal_closed frameSound built decoded sourceAt formulaRun).2
  have body := (goalFormula_spec formulaRun).2
  simpa only [entryDeclaration, body, Body.formula] using Roles.Numeric.named_failure_iff model closed

#print axioms selected_goal_closed
#print axioms selected_goal_negated

theorem goalDocument_negated {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
      proposed negatedLabel groupLabel labels text}
    (success : goalDocument frame maxDepth files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals
      proposed negatedLabel groupLabel labels = .ok text) :
    ∃ (output : Output) (read : BundleRead), ∃ source formula, ∃ (sources : List (String × String)), ∃ negated group rows,
      build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      readBundle frame files maximumBytes = .ok read ∧
      SourceRows.sourceItem read.bundle output.prepared.item = some source ∧
      source.2 ∈ entriesOf read.bundle (keptItems read.items cited (some output.prepared.item)) ∧
      source.2.role = .conjecture ∧ formula.Within [] ∧
      negated = SourceRows.negatedText negatedLabel source.2.original.name formula ∧
      SourceRows.Reads maxDepth negated (SourceRows.negatedEntry negatedLabel formula) ∧
      text = String.join (sources.map (fun row => row.2 ++ "\n")) ++ negated ++ "\n" ++ group ++ String.join rows ∧
      (∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
        (¬ Roles.Bytes.sentence model (entryDeclaration source.2).original) ↔
          Roles.Bytes.sentence model (.neg formula)) := by
  obtain ⟨output, read, source, formula, _, sources, negated, _, group, rows,
    built, readRun, sourceAt, formulaRun, _, _, _, negatedRun, _, _, _, textEq, _⟩ := goalDocument_spec success
  have closed := selected_goal_closed frameSound built readRun sourceAt formulaRun
  have negative := SourceRows.negatedRow_spec negatedRun
  exact ⟨output, read, source, formula, sources, negated, group, rows,
    built, readRun, sourceAt, closed.1, (goalFormula_spec formulaRun).1, closed.2,
    negative.1, negative.2, textEq, selected_goal_negated frameSound built readRun sourceAt formulaRun⟩

#print axioms goalDocument_negated
end Fang.TptpCandidate.CitedDocument
