/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft: not accepted until the next full proof gate. -/
import Fang.FOF.TSTP.ParsedEndpoint

namespace Fang.FofTstpExport.RenderProof
open TstpExport.BuilderProof

def ClauseNameClass (problem : TstpExport.NamedProblem) (name : String) : Prop :=
  name ∈ problem.names ∨ ∃ kind node, name = generatedName kind node

theorem collected_name_class (problem : TstpExport.NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (rows : List TstpExport.Row) (labels : List (Nat × String))
    (disjoint : DisjointNames problem.names) (unique : problem.names.Nodup)
    (trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses)
    (success : collect problem certificate clauses = .ok (rows, labels)) :
    ∀ row ∈ rows, ClauseNameClass problem row.name := by
  simp only [collect, collectWith_eq_run] at success
  cases ran : runCollector problem certificate clauses with
  | error reason => simp [ran, bind, Except.bind] at success
  | ok state =>
    have pair : (state.1, state.2.1) = (rows, labels) := by
      simpa [ran, bind, Except.bind, pure, Except.pure] using success
    have history := (runCollector_derives_disjoint problem certificate clauses state disjoint unique trace ran).1
    have rowEq := (Prod.mk.inj pair).1
    intro row member
    have member : row ∈ state.1 := by simpa only [rowEq] using member
    rcases history row member with ⟨index, _, found⟩ | ⟨kind, node, _, name⟩
    · exact Or.inl (List.mem_of_getElem? found)
    · exact Or.inr ⟨kind, node, name⟩

theorem builder_name_class {problem : TstpExport.NamedProblem} {certificate : Certificate}
    {output : TstpExport.Export} (disjoint : DisjointNames problem.names) (unique : problem.names.Nodup)
    (built : TstpExport.build problem certificate = .ok output) :
    ∀ row ∈ output.rows, ClauseNameClass problem row.name := by
  obtain ⟨clauses, rows, labels, trace, collected, finished⟩ := build_collects built
  rw [finish_rows problem certificate rows labels output finished]
  exact collected_name_class problem certificate clauses rows labels disjoint unique trace collected

theorem fof_builder_name_class {input : String} {decoded : FOFFrontend.Decoded}
    (decodedOk : FOFFrontend.decode input = .ok decoded)
    {certificate : Certificate} {output : Export} (built : build decoded certificate = .ok output) :
    ∀ row ∈ output.trace.rows, ClauseNameClass (traceProblem decoded output.leaves) row.name :=
  builder_name_class (collectLeaves_generated_disjoint (build_source built).2)
    (collectLeaves_names_nodup (decoded_source_names_unique decodedOk) (build_source built).2)
    (build_trace built)

theorem source_leaf_name_distinct {input : String} {decoded : FOFFrontend.Decoded}
    (decodedOk : FOFFrontend.decode input = .ok decoded)
    {certificate : Certificate} {output : Export} (built : build decoded certificate = .ok output)
    {index : Nat} {name : String} {body : GroundFOF.Formula} {leaf : Leaf}
    (sourceBody : decoded.declarations[index]? = some (.fof body))
    (sourceName : decoded.state.clauseNames[index]? = some name)
    (member : leaf ∈ output.leaves) : name ≠ leaf.rawName := by
  have collected := (build_source built).2
  have lower := collectLeaves_lower_sources collected name (List.mem_of_getElem? sourceName)
  obtain ⟨_, _, _, _, _, raw⟩ := collectLeaves_origin collected member
  obtain ⟨bodyAt, nameAt, _⟩ := leaves_origin collected member
  cases shape : leaf.body with
  | fof formula =>
    have raw : leaf.rawName = leafName leaf.declaration leaf.localClause := by simpa only [shape] using raw
    rw [raw]
    exact source_leaf_distinct name _ _ lower
  | cnf clause =>
    have raw : leaf.rawName = leaf.sourceName := by simpa only [shape] using raw
    intro collision
    have sameName : name = leaf.sourceName := collision.trans raw
    have sameIndex : leaf.declaration = index :=
      (List.Nodup.getElem?_inj (List.getElem?_eq_some_iff.mp nameAt).1
        (decoded_source_names_unique decodedOk)).mp
        (nameAt.trans (by simpa only [sameName] using sourceName.symm))
    rw [sameIndex, sourceBody] at bodyAt
    simp [shape] at bodyAt

theorem source_clause_name_distinct {input : String} {decoded : FOFFrontend.Decoded}
    (decodedOk : FOFFrontend.decode input = .ok decoded)
    {certificate : Certificate} {output : Export} (built : build decoded certificate = .ok output)
    {index : Nat} {name : String} {body : GroundFOF.Formula} {row : TstpExport.Row}
    (sourceBody : decoded.declarations[index]? = some (.fof body))
    (sourceName : decoded.state.clauseNames[index]? = some name)
    (member : row ∈ output.trace.rows) : name ≠ row.name := by
  rcases fof_builder_name_class decodedOk built row member with leafName | ⟨kind, node, generated⟩
  · obtain ⟨leaf, leafMember, same⟩ := List.mem_map.mp leafName
    rw [← same]
    exact source_leaf_name_distinct decodedOk built sourceBody sourceName leafMember
  · rw [generated]
    exact source_generated_distinct name kind node
      (collectLeaves_lower_sources (build_source built).2 name (List.mem_of_getElem? sourceName))

def Event.sourceIndex : Event → Option Nat
  | .source index _ _ => some index
  | _ => none

theorem trace_source_ids_fresh {exported rows before after events}
    (trace : TraceEvents exported rows before after events) :
    (events.filterMap Event.sourceIndex).Nodup ∧
      ∀ index ∈ events.filterMap Event.sourceIndex, index ∉ before := by
  induction trace with
  | nil => simp
  | cons head tail ih =>
    cases head with
    | derived notInput =>
      simpa [List.filterMap_append, List.filterMap_cons, Event.sourceIndex] using ih
    | cnf input shape =>
      simpa [List.filterMap_append, List.filterMap_cons, Event.sourceIndex] using ih
    | seen input shape seen =>
      simpa [List.filterMap_append, List.filterMap_cons, Event.sourceIndex] using ih
    | @fresh leaf body input shape absent =>
      simp only [List.filterMap_append, List.filterMap_cons, Event.sourceIndex,
        List.filterMap_nil, List.singleton_append]
      refine ⟨List.nodup_cons.mpr ⟨?_, ih.1⟩, ?_⟩
      · intro member
        exact ih.2 leaf.declaration member (by simp)
      · intro index member already
        rcases List.mem_cons.mp member with same | later
        · exact absent (same ▸ already)
        · exact ih.2 index later (List.mem_cons_of_mem _ already)

end Fang.FofTstpExport.RenderProof
