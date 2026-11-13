/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.EventDecoding

namespace Fang.FofTstpExport.RenderProof
open FofTstpText TstpText

theorem row_events_last {exported row before after events}
    (step : RowEvents exported row before after events) :
    ∃ event, events.getLast? = some event ∧ event.clauseView = some (row.name, row.clause) := by
  cases step with
  | derived _ => exact ⟨.inherited row, rfl, rfl⟩
  | cnf _ _ => exact ⟨.inherited row, rfl, rfl⟩
  | @seen leaf body input shape seen =>
    obtain ⟨_, _, _, _, name, clause⟩ := input
    exact ⟨.clausify leaf, rfl, by simp [Event.clauseView, name, clause]⟩
  | @fresh leaf body input shape absent =>
    obtain ⟨_, _, _, _, name, clause⟩ := input
    exact ⟨.clausify leaf, rfl, by simp [Event.clauseView, name, clause]⟩

theorem trace_events_last {exported rows before after events last}
    (trace : TraceEvents exported rows before after events) (lastAt : rows.getLast? = some last) :
    ∃ event, events.getLast? = some event ∧ event.clauseView = some (last.name, last.clause) := by
  induction rows generalizing before events with
  | nil => simp at lastAt
  | cons row rows ih =>
    cases trace with
    | cons head tail =>
      cases rows with
      | nil =>
        cases tail
        have same : row = last := by simpa using lastAt
        simpa only [List.append_nil, same] using row_events_last head
      | cons next rest =>
        obtain ⟨event, found, value⟩ := ih tail (by simpa using lastAt)
        exact ⟨event, by simp [List.getLast?_append, found], value⟩

/-- The generic list lemma also used by the CNF text proof. -/
theorem related_last_event {relation : α → β → Prop} {left : List α} {right : List β}
    (related : Source.RelatedLists relation left right) {last : α}
    (found : left.getLast? = some last) :
    ∃ output, right.getLast? = some output ∧ relation last output := by
  induction related with
  | nil => simp at found
  | @cons first output rest outputs head tail ih =>
    cases rest with
    | nil =>
      cases tail
      have same : first = last := by simpa using found
      subst last
      exact ⟨output, by simp, head⟩
    | cons next remaining =>
      cases tail with
      | cons nextHead nextTail =>
        obtain ⟨lastOutput, lastFound, related⟩ := ih (by simpa using found)
        exact ⟨lastOutput, by simpa using lastFound, related⟩

theorem EventMeaning.empty_clause {problem label event parsed name}
    (meaning : EventMeaning problem label event parsed)
    (value : event.clauseView = some (name, [])) :
    ∃ role metadata, parsed = .cnf ⟨name, role, [], metadata⟩ := by
  cases meaning with
  | inherited clause source =>
    simp only [Event.clauseView, Option.some.injEq, Prod.mk.injEq] at value
    rw [value.2] at clause
    cases clause
    exact ⟨_, _, by simp only [value.1]; rfl⟩
  | source formula => simp [Event.clauseView] at value
  | clausify clause =>
    simp only [Event.clauseView, Option.some.injEq, Prod.mk.injEq] at value
    rw [value.2] at clause
    cases clause
    exact ⟨_, _, by simp only [value.1]; rfl⟩

theorem decoded_render_parsed_endpoint {input : String} {decoded : FOFFrontend.Decoded}
    (decodedOk : FOFFrontend.decode input = .ok decoded)
    {certificate : Certificate} {exported : Export}
    (built : build decoded certificate = .ok exported)
    {label text : String} (printed : render label exported = .ok text) :
    ∃ seen events parsed, TraceEvents exported exported.trace.rows [] seen events ∧
      Source.RelatedLists (EventMeaning exported.trace.signature label) events parsed ∧
      SourcesBefore [] events ∧
      (∀ event ∈ events, OriginalEvent decoded event) ∧
      EventDerivation exported.trace.signature exported events ∧
      ParsedMixedRows text.toList parsed ∧
      (∀ other, ParsedMixedRows text.toList other → other = parsed) ∧
      (∃ role metadata, parsed.getLast? = some (.cnf ⟨exported.trace.finalName, role, [], metadata⟩)) := by
  obtain ⟨seen, events, texts, parsed, _, trace, meanings, sources, originals, derived, full, unique⟩ :=
    decoded_render_unique_derivation decodedOk built printed
  obtain ⟨_, finalName, finalClause⟩ := build_trace_endpoint built
  cases lastAt : exported.trace.rows.getLast? with
  | none => simp [lastAt] at finalName
  | some row =>
    have name : row.name = exported.trace.finalName := by simpa [lastAt] using finalName
    have clause : row.clause = [] := by simpa [lastAt] using finalClause
    obtain ⟨event, eventAt, value⟩ := trace_events_last trace lastAt
    obtain ⟨lastParsed, parsedAt, meaning⟩ := related_last_event meanings eventAt
    obtain ⟨role, metadata, shape⟩ := meaning.empty_clause (by simpa only [name, clause] using value)
    exact ⟨seen, events, parsed, trace, meanings, sources, originals, derived, full, unique,
      role, metadata, by simpa only [shape] using parsedAt⟩

end Fang.FofTstpExport.RenderProof
