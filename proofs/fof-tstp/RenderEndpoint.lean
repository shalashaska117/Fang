/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.RenderGrammar
import Fang.FOF.TSTP.BuildTrace

namespace Fang.FofTstpExport.RenderProof
open FofTstpText TstpText

/-- The last printed line names the actual trace row and prints its clause.
    Its metadata and role remain available for the separate ancestry proof. -/
def EndsWithRow (problem : TstpExport.NamedProblem) (row : TstpExport.Row)
    (lines : List String) : Prop :=
  ∃ initial text named role metadata, lines = initial ++ [text] ∧
    NamedClause problem row.clause named ∧
    AnnotatedRowText text row.name role named metadata

private theorem existing_ends {problem label row text initial}
    (printed : TstpExport.renderRow problem label row = .ok text) :
    EndsWithRow problem row (initial ++ [text]) := by
  obtain ⟨named, metadata, relation, _, grammar⟩ := row_correspondence label row printed
  exact ⟨initial, text, named, originRole row.origin, metadata, rfl, relation, grammar⟩

private theorem clausified_ends {problem leaf row text initial}
    (sameName : row.name = leaf.rawName) (sameClause : row.clause = leaf.clause)
    (printed : clausifiedRow problem leaf = .ok text) :
    EndsWithRow problem row (initial ++ [text]) := by
  obtain ⟨named, relation, grammar⟩ := clausified_row_correspondence leaf printed
  exact ⟨initial, text, named, .plain, clausificationData leaf, rfl,
    sameClause ▸ relation, sameName ▸ grammar⟩

private theorem inherited_ends (label : String) (exported : Export) (row : TstpExport.Row)
    (before : State) (after : ForInStep State)
    (success : process label exported row before = .ok after)
    (shape : process label exported row before = (do
      let text ← TstpExport.renderRow exported.trace.signature label row
      pure (.yield (before.1, before.2 ++ [text])))) :
    ∃ middle, after = .yield middle ∧ EndsWithRow exported.trace.signature row middle.2 := by
  rw [shape] at success
  cases printed : TstpExport.renderRow exported.trace.signature label row with
  | error reason => simp [printed, bind, Except.bind] at success
  | ok text =>
    have same : .yield (before.1, before.2 ++ [text]) = after := by
      simpa [printed, bind, Except.bind, pure, Except.pure] using success
    exact ⟨_, same.symm, existing_ends printed⟩

theorem process_ends (label : String) (exported : Export) (row : TstpExport.Row)
    (before : State) (after : ForInStep State)
    (success : process label exported row before = .ok after) :
    ∃ middle, after = .yield middle ∧ EndsWithRow exported.trace.signature row middle.2 := by
  cases origin : row.origin with
  | input index name =>
    cases found : exported.leaves[index]? with
    | none => simp [process, origin, found, throw, throwThe, Functor.map, Except.map] at success
    | some leaf =>
      by_cases bad : (row.name != leaf.rawName || !decide (row.clause = leaf.clause)) = true
      · simp [process, origin, found, bad, throw, throwThe, bind, Except.bind] at success
      · have equal : row.name = leaf.rawName ∧ row.clause = leaf.clause := by
          simpa using bad
        cases bodyEq : leaf.body with
        | cnf clause =>
          apply inherited_ends label exported row before after success
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
              exact ⟨_, same.symm, clausified_ends equal.1 equal.2 clauseText⟩
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
                exact ⟨_, same.symm, clausified_ends equal.1 equal.2 clauseText⟩
  | deduplicate node index name =>
    apply inherited_ends label exported row before after success
    simp [process, origin]
  | rename node right name =>
    apply inherited_ends label exported row before after success
    simp [process, origin]
  | factor node first second name substitution =>
    apply inherited_ends label exported row before after success
    simp [process, origin]
  | resolve node first second left right substitution =>
    apply inherited_ends label exported row before after success
    simp [process, origin]

theorem forIn_ends (label : String) (exported : Export) (entries : List TstpExport.Row)
    (before after : State) (last : TstpExport.Row)
    (lastAt : entries.getLast? = some last)
    (success : forIn entries before (process label exported) = .ok after) :
    EndsWithRow exported.trace.signature last after.2 := by
  induction entries generalizing before with
  | nil => simp at lastAt
  | cons row rows ih =>
    cases stepped : process label exported row before with
    | error reason => simp [List.forIn_cons, stepped, bind, Except.bind] at success
    | ok step =>
      obtain ⟨middle, same, ending⟩ := process_ends label exported row before step stepped
      subst step
      have remaining : forIn rows middle (process label exported) = .ok after := by
        simpa [List.forIn_cons, stepped, bind, Except.bind] using success
      cases rows with
      | nil =>
        have rowEq : row = last := by simpa using lastAt
        have stateEq : middle = after := by simpa [pure, Except.pure] using remaining
        simpa only [rowEq, stateEq] using ending
      | cons next rest =>
        apply ih middle
        · simpa using lastAt
        · exact remaining

theorem render_ends (label : String) (exported : Export) (last : TstpExport.Row)
    {text : String} (lastAt : exported.trace.rows.getLast? = some last)
    (printed : render label exported = .ok text) :
    ∃ lines, text = String.join lines ∧ EndsWithRow exported.trace.signature last lines := by
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
        exact ⟨state.2, same.symm,
          forIn_ends label exported exported.trace.rows ([], []) state last lastAt ran⟩

/-- The actual successful FOF build and renderer end with a printed empty CNF
    clause carrying the checked trace's final name. This does not yet connect
    every preceding printed parent and inserted formula to a full derivation. -/
theorem built_render_empty_endpoint {decoded : FOFFrontend.Decoded} {certificate : Certificate}
    {exported : Export} (built : build decoded certificate = .ok exported)
    {label text : String} (printed : render label exported = .ok text) :
    ∃ initial last role metadata,
      text = String.join (initial ++ [last]) ∧
      AnnotatedRowText last exported.trace.finalName role [] metadata := by
  obtain ⟨_, finalName, finalClause⟩ := build_trace_endpoint built
  cases lastAt : exported.trace.rows.getLast? with
  | none => simp [lastAt] at finalName
  | some row =>
    have name : row.name = exported.trace.finalName := by simpa [lastAt] using finalName
    have clause : row.clause = [] := by simpa [lastAt] using finalClause
    obtain ⟨lines, textEq, initial, last, named, role, metadata, lineEq, related, grammar⟩ :=
      render_ends label exported row lastAt printed
    rw [clause] at related
    have namedEq : named = [] := by cases related; rfl
    exact ⟨initial, last, role, metadata, lineEq ▸ textEq,
      by simpa only [name, namedEq] using grammar⟩

end Fang.FofTstpExport.RenderProof
