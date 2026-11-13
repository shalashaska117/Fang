/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.RenderEndpoint

namespace Fang.FofTstpExport.RenderProof
open FofTstpText TstpText

/-- Typed evidence retained for each printed line, including inserted original
    formulas. These are specification objects, not another exporter. -/
inductive Event where
  | inherited (row : TstpExport.Row)
  | source (declaration : Nat) (name : String) (body : GroundFOF.Formula)
  | clausify (leaf : Leaf)

def EventText (problem : TstpExport.NamedProblem) (label : String)
    (event : Event) (text : String) : Prop :=
  match event with
  | .inherited row => RowCorrespondence problem label row text
  | .source _ name body => ∃ named, NamedFormula problem body named ∧
      FormulaRowText text name named (.function "file" [.atom label, .atom name])
  | .clausify leaf => ∃ named, NamedClause problem leaf.clause named ∧
      AnnotatedRowText text leaf.rawName .plain named (clausificationData leaf)

/-- An input event retains its exact leaf lookup, name and clause. -/
def InputLeaf (exported : Export) (row : TstpExport.Row) (leaf : Leaf) : Prop :=
  ∃ index name, row.origin = .input index name ∧ exported.leaves[index]? = some leaf ∧
    row.name = leaf.rawName ∧ row.clause = leaf.clause

inductive RowEvents (exported : Export) (row : TstpExport.Row) :
    List Nat → List Nat → List Event → Prop where
  | derived {seen} (notInput : ∀ index name, row.origin ≠ .input index name) :
      RowEvents exported row seen seen [.inherited row]
  | cnf {seen leaf clause} (input : InputLeaf exported row leaf) (body : leaf.body = .cnf clause) :
      RowEvents exported row seen seen [.inherited row]
  | seen {before leaf body} (input : InputLeaf exported row leaf) (formula : leaf.body = .fof body)
      (already : leaf.declaration ∈ before) :
      RowEvents exported row before before [.clausify leaf]
  | fresh {before leaf body} (input : InputLeaf exported row leaf) (formula : leaf.body = .fof body)
      (absent : leaf.declaration ∉ before) :
      RowEvents exported row before (leaf.declaration :: before)
        [.source leaf.declaration leaf.sourceName body, .clausify leaf]

private theorem inherited_events (label : String) (exported : Export) (row : TstpExport.Row)
    (before : State) (after : ForInStep State)
    (success : process label exported row before = .ok after)
    (step : RowEvents exported row before.1 before.1 [.inherited row])
    (shape : process label exported row before = (do
      let text ← TstpExport.renderRow exported.trace.signature label row
      pure (.yield (before.1, before.2 ++ [text])))) :
    ∃ next events texts, after = .yield (next, before.2 ++ texts) ∧
      RowEvents exported row before.1 next events ∧
      Source.RelatedLists (EventText exported.trace.signature label) events texts := by
  rw [shape] at success
  cases printed : TstpExport.renderRow exported.trace.signature label row with
  | error reason => simp [printed, bind, Except.bind] at success
  | ok text =>
    have same : .yield (before.1, before.2 ++ [text]) = after := by
      simpa [printed, bind, Except.bind, pure, Except.pure] using success
    exact ⟨_, _, [text], same.symm, step, .cons (row_correspondence label row printed) .nil⟩

theorem process_events (label : String) (exported : Export) (row : TstpExport.Row)
    (before : State) (after : ForInStep State)
    (success : process label exported row before = .ok after) :
    ∃ next events texts, after = .yield (next, before.2 ++ texts) ∧
      RowEvents exported row before.1 next events ∧
      Source.RelatedLists (EventText exported.trace.signature label) events texts := by
  cases origin : row.origin with
  | input index name =>
    cases found : exported.leaves[index]? with
    | none => simp [process, origin, found, throw, throwThe, Functor.map, Except.map] at success
    | some leaf =>
      by_cases bad : (row.name != leaf.rawName || !decide (row.clause = leaf.clause)) = true
      · simp [process, origin, found, bad, throw, throwThe, bind, Except.bind] at success
      · have equal : row.name = leaf.rawName ∧ row.clause = leaf.clause := by simpa using bad
        have input : InputLeaf exported row leaf := ⟨index, name, origin, found, equal⟩
        cases bodyEq : leaf.body with
        | cnf clause =>
          apply inherited_events label exported row before after success (.cnf input bodyEq)
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
              exact ⟨_, [.clausify leaf], [text], same.symm, .seen input bodyEq seen,
                .cons (clausified_row_correspondence leaf clauseText) .nil⟩
          · cases formulaText : sourceFormula exported.trace.signature label leaf.sourceName body with
            | error reason =>
              simp [process, origin, found, bad, bodyEq, seen, formulaText, bind, Except.bind] at success
            | ok first =>
              cases clauseText : clausifiedRow exported.trace.signature leaf with
              | error reason =>
                simp [process, origin, found, bad, bodyEq, seen, formulaText, clauseText,
                  bind, Except.bind] at success
              | ok last =>
                have same : .yield (leaf.declaration :: before.1, before.2 ++ [first, last]) = after := by
                  simpa [process, origin, found, bad, bodyEq, seen, formulaText, clauseText,
                    bind, Except.bind, pure, Except.pure] using success
                exact ⟨_, _, [first, last], same.symm, .fresh input bodyEq seen,
                  .cons (source_formula_correspondence formulaText)
                    (.cons (clausified_row_correspondence leaf clauseText) .nil)⟩
  | deduplicate node index name =>
    apply inherited_events label exported row before after success (.derived (by simp [origin]))
    simp [process, origin]
  | rename node right name =>
    apply inherited_events label exported row before after success (.derived (by simp [origin]))
    simp [process, origin]
  | factor node first second name substitution =>
    apply inherited_events label exported row before after success (.derived (by simp [origin]))
    simp [process, origin]
  | resolve node first second left right substitution =>
    apply inherited_events label exported row before after success (.derived (by simp [origin]))
    simp [process, origin]

inductive TraceEvents (exported : Export) :
    List TstpExport.Row → List Nat → List Nat → List Event → Prop where
  | nil {seen} : TraceEvents exported [] seen seen []
  | cons {row rows before middle after first rest}
      (head : RowEvents exported row before middle first)
      (tail : TraceEvents exported rows middle after rest) :
      TraceEvents exported (row :: rows) before after (first ++ rest)

private theorem related_append {relation : α → β → Prop} {left right more extra}
    (first : Source.RelatedLists relation left right)
    (second : Source.RelatedLists relation more extra) :
    Source.RelatedLists relation (left ++ more) (right ++ extra) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem forIn_events (label : String) (exported : Export) (entries : List TstpExport.Row)
    (before after : State)
    (success : forIn entries before (process label exported) = .ok after) :
    ∃ events texts, after.2 = before.2 ++ texts ∧
      TraceEvents exported entries before.1 after.1 events ∧
      Source.RelatedLists (EventText exported.trace.signature label) events texts := by
  induction entries generalizing before with
  | nil =>
    have same : before = after := by simpa [pure, Except.pure] using success
    subst after
    exact ⟨[], [], by simp, .nil, .nil⟩
  | cons row rows ih =>
    cases stepped : process label exported row before with
    | error reason => simp [List.forIn_cons, stepped, bind, Except.bind] at success
    | ok step =>
      obtain ⟨middle, first, printed, same, head, headText⟩ :=
        process_events label exported row before step stepped
      subst step
      have remaining : forIn rows (middle, before.2 ++ printed) (process label exported) = .ok after := by
        simpa [List.forIn_cons, stepped, bind, Except.bind] using success
      obtain ⟨rest, tailText, final, tail, tailTexts⟩ := ih _ remaining
      exact ⟨first ++ rest, printed ++ tailText, by simpa [List.append_assoc] using final,
        .cons head tail, related_append headText tailTexts⟩

theorem render_events (label : String) (exported : Export) {text : String}
    (printed : render label exported = .ok text) :
    ∃ seen events texts, text = String.join texts ∧
      TraceEvents exported exported.trace.rows [] seen events ∧
      Source.RelatedLists (EventText exported.trace.signature label) events texts := by
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
        obtain ⟨events, texts, final, trace, meanings⟩ :=
          forIn_events label exported exported.trace.rows ([], []) state ran
        have final : state.2 = texts := by simpa using final
        exact ⟨state.1, events, texts, by simpa only [final] using same.symm, trace, meanings⟩

end Fang.FofTstpExport.RenderProof
