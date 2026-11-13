/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft: not accepted until the next full proof gate. -/
import Fang.FOF.TSTP.EventNames

namespace Fang.FofTstpExport.RenderProof

def Event.name : Event → String
  | .inherited row => row.name
  | .source _ name _ => name
  | .clausify leaf => leaf.rawName

def Event.sourceName : Event → Option String
  | .source _ name _ => some name
  | _ => none

def sourceNames (events : List Event) : List String := events.filterMap Event.sourceName
def clauseNames (events : List Event) : List String :=
  (events.filterMap Event.clauseView).map Prod.fst

def NamesDisjoint (left right : List String) : Prop :=
  ∀ {name}, name ∈ left → name ∈ right → False

theorem source_name_member {events name} (member : name ∈ sourceNames events) :
    ∃ index body, Event.source index name body ∈ events := by
  obtain ⟨event, atEvent, value⟩ := List.mem_filterMap.mp member
  cases event with
  | inherited row => simp [Event.sourceName] at value
  | clausify leaf => simp [Event.sourceName] at value
  | source index actual body =>
    have same : actual = name := Option.some.inj value
    exact ⟨index, body, same ▸ atEvent⟩

theorem name_member_class {events event} (member : event ∈ events) :
    event.name ∈ sourceNames events ∨ event.name ∈ clauseNames events := by
  cases event with
  | inherited row =>
    exact Or.inr (List.mem_map.mpr ⟨(row.name, row.clause),
      List.mem_filterMap.mpr ⟨_, member, rfl⟩, rfl⟩)
  | source index name body => exact Or.inl (List.mem_filterMap.mpr ⟨_, member, rfl⟩)
  | clausify leaf =>
    exact Or.inr (List.mem_map.mpr ⟨(leaf.rawName, leaf.clause),
      List.mem_filterMap.mpr ⟨_, member, rfl⟩, rfl⟩)

private theorem source_cons_nodup {events : List Event} {name : String}
    (sources : (name :: sourceNames events).Nodup)
    (disjoint : NamesDisjoint (name :: sourceNames events) (clauseNames events))
    (tail : (events.map Event.name).Nodup) : (name :: events.map Event.name).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_, tail⟩
  intro member
  obtain ⟨event, atEvent, same⟩ := List.mem_map.mp member
  rcases name_member_class atEvent with source | clause
  · exact (List.nodup_cons.mp sources).1 (same ▸ source)
  · exact disjoint (by simp) (same ▸ clause)

private theorem clause_cons_nodup {events : List Event} {name : String}
    (clauses : (name :: clauseNames events).Nodup)
    (disjoint : NamesDisjoint (sourceNames events) (name :: clauseNames events))
    (tail : (events.map Event.name).Nodup) : (name :: events.map Event.name).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_, tail⟩
  intro member
  obtain ⟨event, atEvent, same⟩ := List.mem_map.mp member
  rcases name_member_class atEvent with source | clause
  · exact disjoint (same ▸ source) (by simp)
  · exact (List.nodup_cons.mp clauses).1 (same ▸ clause)

theorem partition_names_nodup {events : List Event}
    (sources : (sourceNames events).Nodup) (clauses : (clauseNames events).Nodup)
    (disjoint : NamesDisjoint (sourceNames events) (clauseNames events)) :
    (events.map Event.name).Nodup := by
  induction events with
  | nil => simp
  | cons event events ih =>
    cases event with
    | source index name body =>
      have sources' : (name :: sourceNames events).Nodup := sources
      have clauses' : (clauseNames events).Nodup := clauses
      have disjoint' : NamesDisjoint (name :: sourceNames events) (clauseNames events) := disjoint
      exact source_cons_nodup sources' disjoint'
        (ih (List.nodup_cons.mp sources').2 clauses'
          (fun member other => disjoint' (List.mem_cons_of_mem _ member) other))
    | inherited row =>
      have sources' : (sourceNames events).Nodup := sources
      have clauses' : (row.name :: clauseNames events).Nodup := clauses
      have disjoint' : NamesDisjoint (sourceNames events) (row.name :: clauseNames events) := disjoint
      exact clause_cons_nodup clauses' disjoint'
        (ih sources' (List.nodup_cons.mp clauses').2
          (fun member other => disjoint' member (List.mem_cons_of_mem _ other)))
    | clausify leaf =>
      have sources' : (sourceNames events).Nodup := sources
      have clauses' : (leaf.rawName :: clauseNames events).Nodup := clauses
      have disjoint' : NamesDisjoint (sourceNames events) (leaf.rawName :: clauseNames events) := disjoint
      exact clause_cons_nodup clauses' disjoint'
        (ih sources' (List.nodup_cons.mp clauses').2
          (fun member other => disjoint' member (List.mem_cons_of_mem _ other)))

theorem source_names_related {decoded : FOFFrontend.Decoded} {events : List Event}
    (original : ∀ event ∈ events, OriginalEvent decoded event) :
    Source.RelatedLists (fun index name => decoded.state.clauseNames[index]? = some name)
      (events.filterMap Event.sourceIndex) (sourceNames events) := by
  induction events with
  | nil => exact .nil
  | cons event events ih =>
    have tail := ih (fun event member => original event (List.mem_cons_of_mem _ member))
    cases event with
    | inherited row => exact tail
    | clausify leaf => exact tail
    | source index name body =>
      exact .cons (original (.source index name body) (by simp)).2 tail

theorem related_lookup_nodup {names : List String} (unique : names.Nodup)
    {ids : List Nat} {values : List String}
    (related : Source.RelatedLists (fun index name => names[index]? = some name) ids values)
    (idsUnique : ids.Nodup) : values.Nodup := by
  induction related with
  | nil => simp
  | @cons index name ids names' head tail ih =>
    obtain ⟨absent, remaining⟩ := List.nodup_cons.mp idsUnique
    apply List.nodup_cons.mpr
    refine ⟨?_, ih remaining⟩
    intro duplicate
    obtain ⟨other, member, lookup⟩ := tail.member_right duplicate
    have same : index = other :=
      (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp head).1 unique).mp (head.trans lookup.symm)
    exact absent (same.symm ▸ member)

theorem derivation_names_nodup {problem rows} (derived : TstpExport.Derivation problem rows) :
    (rows.map TstpExport.Row.name).Nodup := by
  induction derived with
  | empty => simp
  | append previous row prior fresh step ih =>
    simp only [List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨ih, by simp, ?_⟩
    intro first firstIn last lastIn same
    obtain ⟨earlier, member, rfl⟩ := List.mem_map.mp firstIn
    have lastEq : last = row.name := List.mem_singleton.mp lastIn
    exact fresh earlier member (same.trans lastEq)

theorem trace_clause_names {exported rows before after events}
    (trace : TraceEvents exported rows before after events) :
    clauseNames events = rows.map TstpExport.Row.name := by
  rw [clauseNames, trace_events_clause_view trace, List.map_map]
  rfl

theorem rendered_event_names_nodup {input : String} {decoded : FOFFrontend.Decoded}
    (decodedOk : FOFFrontend.decode input = .ok decoded)
    {certificate : Certificate} {exported : Export} (built : build decoded certificate = .ok exported)
    {seen events} (trace : TraceEvents exported exported.trace.rows [] seen events) :
    (events.map Event.name).Nodup := by
  have original := trace_events_original built trace
  apply partition_names_nodup
  · exact related_lookup_nodup (decoded_source_names_unique decodedOk)
      (source_names_related original) (trace_source_ids_fresh trace).1
  · rw [trace_clause_names trace]
    exact derivation_names_nodup (decoded_build_typed_derivation decodedOk built)
  · intro name sourceMember clauseMember
    obtain ⟨index, body, member⟩ := source_name_member sourceMember
    obtain ⟨sourceBody, sourceName⟩ := original _ member
    rw [trace_clause_names trace] at clauseMember
    obtain ⟨row, rowIn, same⟩ := List.mem_map.mp clauseMember
    exact source_clause_name_distinct decodedOk built sourceBody sourceName rowIn same.symm

end Fang.FofTstpExport.RenderProof
