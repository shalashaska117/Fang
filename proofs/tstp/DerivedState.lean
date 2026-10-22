/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Freshness

namespace Fang.TstpExport.BuilderProof

def RowInvariant (problem : NamedProblem) (bound : Nat) (state : CollectorState) : Prop :=
  NamesBefore problem bound state ∧ Derivation problem state.1

theorem row_invariant_empty (problem : NamedProblem) (bound : Nat) :
    RowInvariant problem bound ([], [], []) :=
  ⟨names_before_empty problem bound, .empty⟩

theorem row_invariant_labels (problem : NamedProblem) (bound : Nat) (state : CollectorState)
    (labels : List (Nat × String)) (valid : RowInvariant problem bound state) :
    RowInvariant problem bound (state.1, labels, state.2.2) := valid

theorem row_invariant_mono (problem : NamedProblem) (before after : Nat) (state : CollectorState)
    (valid : RowInvariant problem before state) (less : before ≤ after) :
    RowInvariant problem after state :=
  ⟨names_before_mono problem before after state valid.1 less, valid.2⟩

theorem row_invariant_input (problem : NamedProblem) (bound : Nat) (state : CollectorState)
    (source : Nat) (name : String) (raw : Clause)
    (lower : LowerNames problem.names) (unique : problem.names.Nodup)
    (valid : RowInvariant problem bound state)
    (rawAt : problem.signature.problem[source]? = some raw)
    (nameAt : problem.names[source]? = some name) (unseen : source ∉ state.2.2) :
    RowInvariant problem bound
      (state.1 ++ [{ name, clause := raw, origin := .input source name }], state.2.1, source :: state.2.2) := by
  exact ⟨names_before_input problem bound state source name raw valid.1 nameAt,
    .append _ _ valid.2 (source_fresh problem bound state source name lower unique valid.1 nameAt unseen)
      (input_row_justified problem state.1 source name raw rawAt nameAt)⟩

theorem row_invariant_generated (problem : NamedProblem) (node : Nat) (state : CollectorState)
    (row : Row) (kind : NameKind) (lower : LowerNames problem.names)
    (valid : RowInvariant problem node state) (name : row.name = generatedName kind node)
    (justified : Justified problem state.1 row) :
    RowInvariant problem (node + 1) (state.1 ++ [row], state.2.1, state.2.2) := by
  refine ⟨names_before_generated problem (node + 1) state row kind node
    (names_before_mono problem node (node + 1) state valid.1 (by omega)) (by omega) name, ?_⟩
  apply Derivation.append _ _ valid.2 _ justified
  simpa only [name] using generated_fresh problem node state kind lower valid.1

theorem row_invariant_resolution (problem : NamedProblem) (node : Nat) (state : CollectorState)
    (leftName rightName : String) (lc rc result : Clause) (i j : Nat) (σ : Subst)
    (lower : LowerNames problem.names) (valid : RowInvariant problem node state)
    (leftJustified : Justified problem state.1 (leftRow node leftName lc))
    (rightJustified : Justified problem (state.1 ++ [leftRow node leftName lc]) (rightRow node rightName rc))
    (resultJustified : Justified problem (state.1 ++ [leftRow node leftName lc, rightRow node rightName rc])
      (resolveRow node i j σ result)) :
    RowInvariant problem (node + 1)
      (state.1 ++ [leftRow node leftName lc, rightRow node rightName rc, resolveRow node i j σ result],
        state.2.1, state.2.2) := by
  have oldLeft := generated_fresh problem node state .left lower valid.1
  have oldRight := generated_fresh problem node state .right lower valid.1
  have oldStep := generated_fresh problem node state .step lower valid.1
  have freshRight : ∀ row ∈ state.1 ++ [leftRow node leftName lc],
      row.name ≠ (rightRow node rightName rc).name := by
    intro row member
    rcases List.mem_append.mp member with prior | added
    · exact oldRight row prior
    · have same := List.mem_singleton.mp added
      subst row
      intro collision
      have kind := (generated_name_injective (show generatedName .left node = generatedName .right node from collision)).1
      contradiction
  have freshStep : ∀ row ∈ state.1 ++ [leftRow node leftName lc, rightRow node rightName rc],
      row.name ≠ (resolveRow node i j σ result).name := by
    intro row member
    rcases List.mem_append.mp member with prior | added
    · exact oldStep row prior
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at added
      rcases added with same | same
      · subst row
        intro collision
        have kind := (generated_name_injective (show generatedName .left node = generatedName .step node from collision)).1
        contradiction
      · subst row
        intro collision
        have kind := (generated_name_injective (show generatedName .right node = generatedName .step node from collision)).1
        contradiction
  have first := Derivation.append state.1 (leftRow node leftName lc) valid.2 oldLeft leftJustified
  have second := Derivation.append _ (rightRow node rightName rc) first freshRight rightJustified
  have both : Derivation problem (state.1 ++ [leftRow node leftName lc, rightRow node rightName rc]) := by
    simpa only [List.append_assoc, List.singleton_append] using second
  have all := Derivation.append _ (resolveRow node i j σ result) both freshStep resultJustified
  refine ⟨?_, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using all⟩
  have history := names_before_mono problem node (node + 1) state valid.1 (by omega)
  intro row member
  rcases List.mem_append.mp member with prior | added
  · exact history row prior
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at added
    rcases added with same | same | same
    · subst row
      exact Or.inr ⟨.left, node, by omega, rfl⟩
    · subst row
      exact Or.inr ⟨.right, node, by omega, rfl⟩
    · subst row
      exact Or.inr ⟨.step, node, by omega, rfl⟩

end Fang.TstpExport.BuilderProof
