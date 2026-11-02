/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.EventProjection

namespace Fang.FofTstpExport.RenderProof

def EventParent (previous : List Event) (name : String) (clause : Clause) : Prop :=
  ∃ event ∈ previous, event.clauseView = some (name, clause)

/-- The existing inference specification, with parents in the expanded printed
    history. Formula source rows cannot satisfy a clause-parent reference. -/
def EventJustified (problem : TstpExport.NamedProblem) (previous : List Event)
    (row : TstpExport.Row) : Prop :=
  match row.origin with
  | .input i name => problem.names[i]? = some name ∧ row.name = name ∧
      problem.signature.problem[i]? = some row.clause
  | .deduplicate _ i name => ∃ raw, EventParent previous name raw ∧
      problem.signature.problem[i]? = some raw ∧ row.clause = dedup raw
  | .rename _ right name => ∃ parent, EventParent previous name parent ∧
      row.clause = parent.map (Literal.rename (if right then rightRename else leftRename))
  | .factor _ i j name σ => ∃ parent, EventParent previous name parent ∧
      Fang.factor parent i j σ = some row.clause
  | .resolve _ i j left right σ => ∃ lc rc,
      EventParent previous left lc ∧ EventParent previous right rc ∧
      TstpExport.ResolutionWitness lc i rc j σ row.clause

theorem parent_in_events {rows events name clause}
    (view : events.filterMap Event.clauseView = rows.map (fun row : TstpExport.Row => (row.name, row.clause)))
    (parent : TstpExport.Parent rows name clause) : EventParent events name clause := by
  obtain ⟨row, member, nameEq, clauseEq⟩ := parent
  have found : (name, clause) ∈ events.filterMap Event.clauseView := by
    rw [view]
    exact List.mem_map.mpr ⟨row, member, by simp [nameEq, clauseEq]⟩
  exact List.mem_filterMap.mp found

theorem justified_in_events {problem rows events row}
    (view : events.filterMap Event.clauseView = rows.map (fun row : TstpExport.Row => (row.name, row.clause)))
    (justified : TstpExport.Justified problem rows row) : EventJustified problem events row := by
  cases origin : row.origin with
  | input index name => simpa only [TstpExport.Justified, EventJustified, origin] using justified
  | deduplicate node index name =>
    simp only [TstpExport.Justified, EventJustified, origin] at justified ⊢
    obtain ⟨raw, parent, source, clause⟩ := justified
    exact ⟨raw, parent_in_events view parent, source, clause⟩
  | rename node right name =>
    simp only [TstpExport.Justified, EventJustified, origin] at justified ⊢
    obtain ⟨parent, prior, clause⟩ := justified
    exact ⟨parent, parent_in_events view prior, clause⟩
  | factor node i j name substitution =>
    simp only [TstpExport.Justified, EventJustified, origin] at justified ⊢
    obtain ⟨parent, prior, result⟩ := justified
    exact ⟨parent, parent_in_events view prior, result⟩
  | resolve node i j left right substitution =>
    simp only [TstpExport.Justified, EventJustified, origin] at justified ⊢
    obtain ⟨lc, rc, leftParent, rightParent, witness⟩ := justified
    exact ⟨lc, rc, parent_in_events view leftParent, parent_in_events view rightParent, witness⟩

theorem trace_events_split {exported earlierRows suffix before after events}
    (trace : TraceEvents exported (earlierRows ++ suffix) before after events) :
    ∃ middle first rest, events = first ++ rest ∧
      TraceEvents exported earlierRows before middle first ∧
      TraceEvents exported suffix middle after rest := by
  induction earlierRows generalizing before events with
  | nil => exact ⟨before, [], events, rfl, .nil, trace⟩
  | cons row rows ih =>
    cases trace with
    | cons head tail =>
      obtain ⟨middle, first, rest, same, earlier, later⟩ := ih tail
      exact ⟨middle, _, rest, by simp only [same, List.append_assoc], .cons head earlier, later⟩

theorem trace_events_singleton {exported row before after events}
    (trace : TraceEvents exported [row] before after events) :
    RowEvents exported row before after events := by
  cases trace with
  | cons head tail =>
    cases tail
    simpa using head

/-- Each expanded group retains its exact trace row and inference witness, and
    every derived clause parent is already in the printed event history.
    Source-formula ancestry is discharged separately by SourcesBefore. -/
inductive EventDerivation (problem : TstpExport.NamedProblem) (exported : Export) :
    List Event → Prop where
  | empty : EventDerivation problem exported []
  | append {previous row before after events}
      (prior : EventDerivation problem exported previous)
      (expansion : RowEvents exported row before after events)
      (step : EventJustified problem previous row) :
      EventDerivation problem exported (previous ++ events)

theorem derivation_in_events {problem exported rows}
    (derived : TstpExport.Derivation problem rows)
    {before after events} (trace : TraceEvents exported rows before after events) :
    EventDerivation problem exported events := by
  induction derived generalizing before after events with
  | empty => cases trace; exact .empty
  | append previous row prior fresh step ih =>
    obtain ⟨middle, first, rest, same, earlier, last⟩ := trace_events_split trace
    rw [same]
    exact .append (ih earlier) (trace_events_singleton last)
      (justified_in_events (trace_events_clause_view earlier) step)

theorem decoded_render_derivation {input : String} {decoded : FOFFrontend.Decoded}
    (decodedOk : FOFFrontend.decode input = .ok decoded)
    {certificate : Certificate} {exported : Export}
    (built : build decoded certificate = .ok exported)
    {label text : String} (printed : render label exported = .ok text) :
    ∃ seen events texts, text = String.join texts ∧
      TraceEvents exported exported.trace.rows [] seen events ∧
      Source.RelatedLists (EventText exported.trace.signature label) events texts ∧
      SourcesBefore [] events ∧
      (∀ event ∈ events, OriginalEvent decoded event) ∧
      EventDerivation exported.trace.signature exported events := by
  obtain ⟨seen, events, texts, same, trace, meanings, sources⟩ := built_render_sources built printed
  exact ⟨seen, events, texts, same, trace, meanings, sources,
    trace_events_original built trace,
    derivation_in_events (decoded_build_typed_derivation decodedOk built) trace⟩

end Fang.FofTstpExport.RenderProof
