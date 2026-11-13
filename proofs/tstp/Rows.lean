/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Acceptance

namespace Fang.TstpExport

/-- Resolution between the already standardized clauses printed as parents.
    Applying the standardization maps a second time would change the witness. -/
def ResolutionWitness (left : Clause) (i : Nat) (right : Clause) (j : Nat)
    (σ : Subst) (result : Clause) : Prop :=
  ∃ a b, left[i]? = some a ∧ right[j]? = some b ∧
    a.positive ≠ b.positive ∧ a.atom.subst σ = b.atom.subst σ ∧
    substUnique σ = true ∧
    result = (left.eraseIdx i).map (Literal.subst σ) ++
      (right.eraseIdx j).map (Literal.subst σ)

def Parent (previous : List Row) (name : String) (clause : Clause) : Prop :=
  ∃ row ∈ previous, row.name = name ∧ row.clause = clause

/-- Independent typed-row specification. Numeric certificate-node witnesses
    still need a separate correspondence to the original certificate. -/
def Justified (problem : NamedProblem) (previous : List Row) (row : Row) : Prop :=
  match row.origin with
  | .input i name => problem.names[i]? = some name ∧ row.name = name ∧
      problem.signature.problem[i]? = some row.clause
  | .deduplicate _ i name => ∃ raw, Parent previous name raw ∧
      problem.signature.problem[i]? = some raw ∧ row.clause = dedup raw
  | .rename _ right name => ∃ parent, Parent previous name parent ∧
      row.clause = parent.map (Literal.rename (if right then rightRename else leftRename))
  | .factor _ i j name σ => ∃ parent, Parent previous name parent ∧
      Fang.factor parent i j σ = some row.clause
  | .resolve _ i j left right σ => ∃ lc rc,
      Parent previous left lc ∧ Parent previous right rc ∧
      ResolutionWitness lc i rc j σ row.clause

inductive Derivation (problem : NamedProblem) : List Row → Prop where
  | empty : Derivation problem []
  | append (previous : List Row) (row : Row)
      (prior : Derivation problem previous)
      (fresh : ∀ earlier ∈ previous, earlier.name ≠ row.name)
      (step : Justified problem previous row) : Derivation problem (previous ++ [row])

theorem resolutionWitness_valid {D : Type} (M : Interpretation D)
    (left right result : Clause) (i j : Nat) (σ : Subst)
    (hl : left.Valid M) (hr : right.Valid M)
    (h : ResolutionWitness left i right j σ result) : result.Valid M := by
  obtain ⟨a, b, hai, hbj, opposite, same, _, rfl⟩ := h
  intro ρ
  let ρ' := fun v => (lookup σ v).eval M ρ
  rcases holds_split M ρ' left i a hai (hl ρ') with ha | leftRest
  · rcases holds_split M ρ' right j b hbj (hr ρ') with hb | rightRest
    · exact False.elim (opposite_inconsistent M ρ (a.subst σ) (b.subst σ)
        opposite same ((Literal.holds_subst M ρ σ a).mpr ha)
        ((Literal.holds_subst M ρ σ b).mpr hb))
    · obtain ⟨l, member, holds⟩ := (holds_subst_map M ρ σ (right.eraseIdx j)).mpr rightRest
      exact ⟨l, List.mem_append_right _ member, holds⟩
  · obtain ⟨l, member, holds⟩ := (holds_subst_map M ρ σ (left.eraseIdx i)).mpr leftRest
    exact ⟨l, List.mem_append_left _ member, holds⟩

theorem parent_valid {D : Type} (M : Interpretation D) (previous : List Row)
    (name : String) (clause : Clause)
    (valid : ∀ row ∈ previous, row.clause.Valid M)
    (h : Parent previous name clause) : clause.Valid M := by
  obtain ⟨row, member, _, rfl⟩ := h
  exact valid row member

theorem justified_valid {D : Type} (M : Interpretation D) (problem : NamedProblem)
    (previous : List Row) (row : Row)
    (hp : problem.signature.problem.Models M)
    (prior : ∀ earlier ∈ previous, earlier.clause.Valid M)
    (h : Justified problem previous row) : row.clause.Valid M := by
  cases ho : row.origin with
  | input i name =>
    simp only [Justified, ho] at h
    exact hp row.clause (List.mem_iff_getElem?.mpr ⟨i, h.2.2⟩)
  | deduplicate node i name =>
    simp only [Justified, ho] at h
    obtain ⟨raw, parent, _, result⟩ := h
    rw [result]
    exact (dedup_preserves_models M raw).mpr (parent_valid M previous name raw prior parent)
  | rename node right name =>
    simp only [Justified, ho] at h
    obtain ⟨parent, source, result⟩ := h
    rw [result]
    exact Clause.valid_rename M _ parent (parent_valid M previous name parent prior source)
  | factor node i j name σ =>
    simp only [Justified, ho] at h
    obtain ⟨parent, source, result⟩ := h
    exact factor_valid M parent row.clause i j σ
      (parent_valid M previous name parent prior source) result
  | resolve node i j left right σ =>
    simp only [Justified, ho] at h
    obtain ⟨lc, rc, lh, rh, result⟩ := h
    exact resolutionWitness_valid M lc rc row.clause i j σ
      (parent_valid M previous left lc prior lh)
      (parent_valid M previous right rc prior rh) result

theorem derivation_valid {D : Type} (M : Interpretation D) (problem : NamedProblem)
    (rows : List Row) (hp : problem.signature.problem.Models M)
    (h : Derivation problem rows) : ∀ row ∈ rows, row.clause.Valid M := by
  induction h with
  | empty => simp
  | append previous row _ _ step ih =>
    intro current member
    rcases List.mem_append.mp member with before | last
    · exact ih current before
    · have same : current = row := List.mem_singleton.mp last
      subst current
      exact justified_valid M problem previous row hp ih step

theorem derivation_empty_unsat (problem : NamedProblem) (rows : List Row)
    (h : Derivation problem rows) (empty : ∃ row ∈ rows, row.clause = []) :
    ¬ Satisfiable problem.signature.problem := by
  rintro ⟨D, ⟨d⟩, M, hp⟩
  obtain ⟨row, member, isEmpty⟩ := empty
  have valid := derivation_valid M problem rows hp h row member
  rw [isEmpty] at valid
  obtain ⟨literal, member, _⟩ := valid (fun _ => d)
  simp at member

end Fang.TstpExport
