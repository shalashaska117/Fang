/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.EventSources

namespace Fang.FofTstpExport.RenderProof

def Event.clauseView : Event → Option (String × Clause)
  | .inherited row => some (row.name, row.clause)
  | .source _ _ _ => none
  | .clausify leaf => some (leaf.rawName, leaf.clause)

theorem row_events_clause_view {exported row before after events}
    (step : RowEvents exported row before after events) :
    events.filterMap Event.clauseView = [(row.name, row.clause)] := by
  cases step with
  | derived _ => rfl
  | cnf _ _ => rfl
  | seen input _ _ =>
    obtain ⟨_, _, _, _, name, clause⟩ := input
    rw [name, clause]
    rfl
  | fresh input _ _ =>
    obtain ⟨_, _, _, _, name, clause⟩ := input
    rw [name, clause]
    rfl

/-- Inserting FOF source formulas neither drops nor reorders clause rows. -/
theorem trace_events_clause_view {exported rows before after events}
    (trace : TraceEvents exported rows before after events) :
    events.filterMap Event.clauseView = rows.map (fun row => (row.name, row.clause)) := by
  induction trace with
  | nil => rfl
  | cons head tail ih => simp [List.filterMap_append, row_events_clause_view head, ih]

def OriginalEvent (decoded : FOFFrontend.Decoded) : Event → Prop
  | .inherited _ => True
  | .source index name body =>
      decoded.declarations[index]? = some (.fof body) ∧
      decoded.state.clauseNames[index]? = some name
  | .clausify leaf =>
      decoded.declarations[leaf.declaration]? = some leaf.body ∧
      decoded.state.clauseNames[leaf.declaration]? = some leaf.sourceName ∧
      leaf.body.clauses[leaf.localClause]? = some leaf.clause

theorem row_events_original {decoded : FOFFrontend.Decoded} {certificate : Certificate}
    {exported : Export} (built : build decoded certificate = .ok exported)
    {row before after events} (step : RowEvents exported row before after events) :
    ∀ event ∈ events, OriginalEvent decoded event := by
  cases step with
  | derived _ => simp [OriginalEvent]
  | cnf _ _ => simp [OriginalEvent]
  | @seen leaf body input shape seen =>
    obtain ⟨index, _, _, found, _, _⟩ := input
    have origin := leaves_origin (build_source built).2 (List.mem_of_getElem? found)
    simpa [OriginalEvent] using origin
  | @fresh leaf body input shape absent =>
    obtain ⟨index, _, _, found, _, _⟩ := input
    have origin := leaves_origin (build_source built).2 (List.mem_of_getElem? found)
    have source : OriginalEvent decoded (.source leaf.declaration leaf.sourceName body) :=
      ⟨by simpa only [shape] using origin.1, origin.2.1⟩
    intro event member
    rcases List.mem_cons.mp member with same | later
    · simpa only [same] using source
    · have same : event = .clausify leaf := List.mem_singleton.mp later
      simpa only [same, OriginalEvent] using origin

theorem trace_events_original {decoded : FOFFrontend.Decoded} {certificate : Certificate}
    {exported : Export} (built : build decoded certificate = .ok exported)
    {rows before after events} (trace : TraceEvents exported rows before after events) :
    ∀ event ∈ events, OriginalEvent decoded event := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    intro event member
    rcases List.mem_append.mp member with first | later
    · exact row_events_original built head event first
    · exact ih event later

theorem original_clausification_valid {D : Type} (model : Interpretation D)
    {decoded : FOFFrontend.Decoded} {leaf : Leaf}
    (origin : OriginalEvent decoded (.clausify leaf))
    (original : GroundFOF.DeclarationsModels model decoded.declarations) : leaf.clause.Valid model :=
  original_declaration_consequence model decoded.declarations leaf.declaration leaf.localClause
    leaf.body leaf.clause origin.1 origin.2.2 original

end Fang.FofTstpExport.RenderProof
