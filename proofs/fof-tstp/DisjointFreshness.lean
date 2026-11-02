/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Generalizes proofs/tstp/Freshness.lean without changing the builder. -/
import Derivation

namespace Fang.TstpExport.BuilderProof

/-- Source leaf labels need not use the input identifier grammar. They must
    remain distinct from every generated resolution/factoring label. -/
def DisjointNames (names : List String) : Prop :=
  ∀ name ∈ names, ∀ kind node, name ≠ generatedName kind node

theorem lower_names_disjoint {names : List String} (lower : LowerNames names) :
    DisjointNames names := by
  intro name member kind node
  exact source_generated_distinct name kind node (lower name member)

theorem generated_fresh_disjoint (problem : NamedProblem) (node : Nat) (state : CollectorState)
    (kind : NameKind) (disjoint : DisjointNames problem.names)
    (history : NamesBefore problem node state) :
    ∀ row ∈ state.1, row.name ≠ generatedName kind node := by
  intro row member equal
  rcases history row member with ⟨source, _, sourceAt⟩ | ⟨priorKind, prior, less, priorName⟩
  · exact disjoint row.name (List.mem_iff_getElem?.mpr ⟨source, sourceAt⟩) kind node equal
  · have same := (generated_name_injective (priorName.symm.trans equal)).2
    omega

theorem source_fresh_disjoint (problem : NamedProblem) (bound : Nat) (state : CollectorState)
    (source : Nat) (name : String) (disjoint : DisjointNames problem.names)
    (unique : problem.names.Nodup) (history : NamesBefore problem bound state)
    (sourceAt : problem.names[source]? = some name) (unseen : source ∉ state.2.2) :
    ∀ row ∈ state.1, row.name ≠ name := by
  intro row member equal
  rcases history row member with ⟨other, seen, otherAt⟩ | ⟨kind, node, _, generated⟩
  · have sourceBound := (List.getElem?_eq_some_iff.mp sourceAt).1
    have same : source = other :=
      (List.Nodup.getElem?_inj sourceBound unique).mp (sourceAt.trans (by simpa [equal] using otherAt.symm))
    exact unseen (same ▸ seen)
  · exact disjoint name (List.mem_iff_getElem?.mpr ⟨source, sourceAt⟩) kind node
      (equal.symm.trans generated)

end Fang.TstpExport.BuilderProof
