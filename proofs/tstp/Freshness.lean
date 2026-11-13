/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Names

namespace Fang.TstpExport.BuilderProof

/-- Every existing label is a recorded source name or belongs to an earlier
    certificate node. This predicate does not assume row-name uniqueness. -/
def NamesBefore (problem : NamedProblem) (bound : Nat) (state : CollectorState) : Prop :=
  ∀ row ∈ state.1,
    (∃ source, source ∈ state.2.2 ∧ problem.names[source]? = some row.name) ∨
    ∃ kind node, node < bound ∧ row.name = generatedName kind node

theorem names_before_empty (problem : NamedProblem) (bound : Nat) :
    NamesBefore problem bound ([], [], []) := by simp [NamesBefore]

theorem names_before_mono (problem : NamedProblem) (before after : Nat) (state : CollectorState)
    (history : NamesBefore problem before state) (bound : before ≤ after) :
    NamesBefore problem after state := by
  intro row member
  rcases history row member with source | ⟨kind, node, less, name⟩
  · exact Or.inl source
  · exact Or.inr ⟨kind, node, Nat.lt_of_lt_of_le less bound, name⟩

theorem names_before_labels (problem : NamedProblem) (bound : Nat) (state : CollectorState)
    (labels : List (Nat × String)) (history : NamesBefore problem bound state) :
    NamesBefore problem bound (state.1, labels, state.2.2) := history

theorem names_before_input (problem : NamedProblem) (bound : Nat) (state : CollectorState)
    (source : Nat) (name : String) (raw : Clause)
    (history : NamesBefore problem bound state) (sourceAt : problem.names[source]? = some name) :
    NamesBefore problem bound
      (state.1 ++ [{ name, clause := raw, origin := .input source name }], state.2.1, source :: state.2.2) := by
  intro row member
  rcases List.mem_append.mp member with earlier | added
  · rcases history row earlier with ⟨other, seen, nameAt⟩ | generated
    · exact Or.inl ⟨other, List.mem_cons_of_mem _ seen, nameAt⟩
    · exact Or.inr generated
  · have same := List.mem_singleton.mp added
    subst row
    exact Or.inl ⟨source, by simp, sourceAt⟩

theorem names_before_generated (problem : NamedProblem) (bound : Nat) (state : CollectorState)
    (row : Row) (kind : NameKind) (node : Nat)
    (history : NamesBefore problem bound state) (less : node < bound)
    (name : row.name = generatedName kind node) :
    NamesBefore problem bound (state.1 ++ [row], state.2.1, state.2.2) := by
  intro current member
  rcases List.mem_append.mp member with earlier | added
  · exact history current earlier
  · have same := List.mem_singleton.mp added
    subst current
    exact Or.inr ⟨kind, node, less, name⟩

theorem generated_fresh (problem : NamedProblem) (node : Nat) (state : CollectorState)
    (kind : NameKind) (lower : LowerNames problem.names)
    (history : NamesBefore problem node state) :
    ∀ row ∈ state.1, row.name ≠ generatedName kind node := by
  intro row member equal
  rcases history row member with ⟨source, _, sourceAt⟩ | ⟨priorKind, prior, less, priorName⟩
  · exact source_generated_distinct row.name kind node
      (lower row.name (List.mem_iff_getElem?.mpr ⟨source, sourceAt⟩)) equal
  · have same := (generated_name_injective (priorName.symm.trans equal)).2
    omega

theorem source_fresh (problem : NamedProblem) (bound : Nat) (state : CollectorState)
    (source : Nat) (name : String) (lower : LowerNames problem.names)
    (unique : problem.names.Nodup) (history : NamesBefore problem bound state)
    (sourceAt : problem.names[source]? = some name) (unseen : source ∉ state.2.2) :
    ∀ row ∈ state.1, row.name ≠ name := by
  intro row member equal
  rcases history row member with ⟨other, seen, otherAt⟩ | ⟨kind, node, _, generated⟩
  · have sourceBound := (List.getElem?_eq_some_iff.mp sourceAt).1
    have same : source = other :=
      (List.Nodup.getElem?_inj sourceBound unique).mp (sourceAt.trans (by simpa [equal] using otherAt.symm))
    exact unseen (same ▸ seen)
  · have valid := lower name (List.mem_iff_getElem?.mpr ⟨source, sourceAt⟩)
    exact source_generated_distinct name kind node valid (equal.symm.trans generated)

end Fang.TstpExport.BuilderProof
