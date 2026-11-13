/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.RenderProcess

namespace Fang.FofTstpExport.RenderProof
open FofTstpText TstpText

def LinesHaveSyntax (lines : List String) : Prop :=
  ∃ rows, Source.RelatedLists MixedRowText lines rows

private theorem related_append {relation : α → β → Prop} {left right more extra}
    (first : Source.RelatedLists relation left right)
    (second : Source.RelatedLists relation more extra) :
    Source.RelatedLists relation (left ++ more) (right ++ extra) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem LinesHaveSyntax.append_row {lines text row}
    (before : LinesHaveSyntax lines) (grammar : MixedRowText text row) :
    LinesHaveSyntax (lines ++ [text]) := by
  obtain ⟨rows, parsed⟩ := before
  exact ⟨rows ++ [row], related_append parsed (.cons grammar .nil)⟩

private theorem append_existing {problem label row text lines}
    (before : LinesHaveSyntax lines)
    (printed : TstpExport.renderRow problem label row = .ok text) :
    LinesHaveSyntax (lines ++ [text]) := by
  obtain ⟨named, metadata, _, _, grammar⟩ := row_correspondence label row printed
  exact before.append_row (row := .cnf ⟨row.name, originRole row.origin, named, metadata⟩) grammar

private theorem append_formula {problem label name body text lines}
    (before : LinesHaveSyntax lines)
    (printed : sourceFormula problem label name body = .ok text) :
    LinesHaveSyntax (lines ++ [text]) := by
  obtain ⟨named, _, grammar⟩ := source_formula_correspondence printed
  exact before.append_row (row := .fof name named (.function "file" [.atom label, .atom name])) grammar

private theorem append_clausified {problem leaf text lines}
    (before : LinesHaveSyntax lines)
    (printed : clausifiedRow problem leaf = .ok text) :
    LinesHaveSyntax (lines ++ [text]) := by
  obtain ⟨named, _, grammar⟩ := clausified_row_correspondence leaf printed
  exact before.append_row (row := .cnf ⟨leaf.rawName, .plain, named, clausificationData leaf⟩) grammar

private theorem inherited_preserves (label : String) (exported : Export) (row : TstpExport.Row)
    (before : State) (after : ForInStep State) (valid : LinesHaveSyntax before.2)
    (success : process label exported row before = .ok after)
    (shape : process label exported row before = (do
      let text ← TstpExport.renderRow exported.trace.signature label row
      pure (.yield (before.1, before.2 ++ [text])))) :
    ∃ middle, after = .yield middle ∧ LinesHaveSyntax middle.2 := by
  rw [shape] at success
  cases printed : TstpExport.renderRow exported.trace.signature label row with
  | error reason => simp [printed, bind, Except.bind] at success
  | ok text =>
    have same : .yield (before.1, before.2 ++ [text]) = after := by
      simpa [printed, bind, Except.bind, pure, Except.pure] using success
    exact ⟨_, same.symm, append_existing valid printed⟩

theorem process_preserves_syntax (label : String) (exported : Export) (row : TstpExport.Row)
    (before : State) (after : ForInStep State) (valid : LinesHaveSyntax before.2)
    (success : process label exported row before = .ok after) :
    ∃ middle, after = .yield middle ∧ LinesHaveSyntax middle.2 := by
  cases origin : row.origin with
  | input index name =>
    cases found : exported.leaves[index]? with
    | none => simp [process, origin, found, throw, throwThe, Functor.map, Except.map] at success
    | some leaf =>
      by_cases bad : (row.name != leaf.rawName || !decide (row.clause = leaf.clause)) = true
      · simp [process, origin, found, bad, throw, throwThe, bind, Except.bind] at success
      · cases bodyEq : leaf.body with
        | cnf clause =>
          apply inherited_preserves label exported row before after valid success
          simp [process, origin, found, bad, bodyEq]
        | fof body =>
          by_cases seen : leaf.declaration ∈ before.1
          · cases clauseText : clausifiedRow exported.trace.signature leaf with
            | error reason =>
              simp [process, origin, found, bad, bodyEq, seen, clauseText, bind, Except.bind] at success
            | ok text =>
              have same : .yield (before.1, before.2 ++ [text]) = after := by
                simpa [process, origin, found, bad, bodyEq, seen, clauseText,
                  bind, Except.bind, pure, Except.pure] using success
              exact ⟨_, same.symm, append_clausified valid clauseText⟩
          · cases formulaText : sourceFormula exported.trace.signature label leaf.sourceName body with
            | error reason =>
              simp [process, origin, found, bad, bodyEq, seen, formulaText, bind, Except.bind] at success
            | ok first =>
              cases clauseText : clausifiedRow exported.trace.signature leaf with
              | error reason =>
                simp [process, origin, found, bad, bodyEq, seen, formulaText, clauseText,
                  bind, Except.bind] at success
              | ok last =>
                have same : .yield (leaf.declaration :: before.1, (before.2 ++ [first]) ++ [last]) = after := by
                  simpa [process, origin, found, bad, bodyEq, seen, formulaText, clauseText,
                    bind, Except.bind, pure, Except.pure] using success
                exact ⟨_, same.symm, append_clausified (append_formula valid formulaText) clauseText⟩
  | deduplicate node index name =>
    apply inherited_preserves label exported row before after valid success
    simp [process, origin]
  | rename node right name =>
    apply inherited_preserves label exported row before after valid success
    simp [process, origin]
  | factor node first second name substitution =>
    apply inherited_preserves label exported row before after valid success
    simp [process, origin]
  | resolve node first second left right substitution =>
    apply inherited_preserves label exported row before after valid success
    simp [process, origin]

theorem forIn_preserves_syntax (label : String) (exported : Export)
    (entries : List TstpExport.Row) (before after : State)
    (valid : LinesHaveSyntax before.2)
    (success : forIn entries before (process label exported) = .ok after) :
    LinesHaveSyntax after.2 := by
  induction entries generalizing before with
  | nil =>
    have same : before = after := by simpa [pure, Except.pure] using success
    simpa [same] using valid
  | cons row rows ih =>
    cases stepped : process label exported row before with
    | error reason => simp [List.forIn_cons, stepped, bind, Except.bind] at success
    | ok step =>
      obtain ⟨middle, same, middleValid⟩ := process_preserves_syntax label exported row before step valid stepped
      subst step
      apply ih middle middleValid
      simpa [List.forIn_cons, stepped, bind, Except.bind] using success

theorem render_syntax (label : String) (exported : Export) {text : String}
    (printed : render label exported = .ok text) :
    ∃ lines, text = String.join lines ∧ LinesHaveSyntax lines ∧
      text.utf8ByteSize ≤ 16 * 1024 * 1024 := by
  rw [render_eq_run] at printed
  cases quoted : TstpExport.quote label with
  | error reason =>
    simp [quoted, discard, Functor.mapConst, Except.map, bind, Except.bind] at printed
  | ok ignored =>
    cases ran : run label exported with
    | error reason =>
      simp [quoted, ran, discard, Functor.mapConst, Except.map, bind, Except.bind] at printed
    | ok state =>
      by_cases large : (String.join state.2).utf8ByteSize > 16 * 1024 * 1024
      · simp [quoted, ran, large, discard, Functor.mapConst, Except.map,
          bind, Except.bind, throw] at printed
      · have same : String.join state.2 = text := by
          simpa [quoted, ran, large, discard, Functor.mapConst, Functor.map, Except.map,
            bind, Except.bind, pure, Except.pure] using printed
        subst text
        exact ⟨state.2, rfl, forIn_preserves_syntax label exported exported.trace.rows ([], []) state
          ⟨[], .nil⟩ ran, by omega⟩

/-- Successful actual rendering has one fully consumed sequence of named rows.
    This is a text-grammar guarantee; trace ancestry and the final empty clause
    still need their separate correspondence to this sequence. -/
theorem render_unique_parse (label : String) (exported : Export) {text : String}
    (printed : render label exported = .ok text) :
    ∃ rows, ParsedMixedRows text.toList rows ∧
      ∀ other, ParsedMixedRows text.toList other → other = rows := by
  obtain ⟨lines, same, ⟨rows, grammar⟩, _⟩ := render_syntax label exported printed
  have parsed : ParsedMixedRows text.toList rows := by
    rw [same]
    exact mixed_rows_parse grammar
  exact ⟨rows, parsed, fun _ other => other.unique parsed⟩

end Fang.FofTstpExport.RenderProof
