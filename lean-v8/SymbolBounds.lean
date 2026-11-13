/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ExistentialExtension

namespace Fang.QuantifiedFOF.Skolem

theorem termBelow_mono {low high : Nat} (le : low ≤ high) (term : Term)
    (below : TermBelow low term) : TermBelow high term := by
  cases term with
  | var id => simp [TermBelow]
  | app symbol arguments =>
    simp only [TermBelow] at below ⊢
    exact ⟨by omega, fun child member => termBelow_mono le child (below.2 child member)⟩
termination_by sizeOf term

theorem formulaBelow_mono {low high : Nat} (le : low ≤ high) (formula : Formula)
    (below : FormulaBelow low formula) : FormulaBelow high formula := by
  induction formula with
  | atom atom => exact fun term member => termBelow_mono le term (below term member)
  | truth | falsity => trivial
  | neg body ih | all id body ih | ex id body ih => exact ih below
  | conj l r il ir | disj l r il ir | implies l r il ir =>
    simp only [FormulaBelow] at below ⊢
    exact ⟨il below.1, ir below.2⟩

theorem term_substitution_below (limit binder : Nat) (replacement term : Term)
    (replacementBelow : TermBelow limit replacement) (below : TermBelow limit term) :
    TermBelow limit (term.subst [(binder, replacement)]) := by
  cases term with
  | var id =>
    by_cases same : binder = id
    · simp [Term.subst, lookup, same, replacementBelow]
    · simp [Term.subst, lookup, same, TermBelow]
  | app symbol arguments =>
    simp only [TermBelow] at below
    simp only [Term.subst, termsSubst_eq_map, TermBelow]
    refine ⟨below.1, ?_⟩
    intro result member
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    exact term_substitution_below limit binder replacement source replacementBelow (below.2 source present)
termination_by sizeOf term

theorem substitution_below (limit binder : Nat) (replacement : Term) (formula : Formula)
    (replacementBelow : TermBelow limit replacement) (below : FormulaBelow limit formula) :
    FormulaBelow limit (substitute binder replacement formula) := by
  induction formula with
  | atom atom =>
    simp only [substitute, FormulaBelow, Atom.subst]
    intro result member
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    exact term_substitution_below limit binder replacement source replacementBelow (below source present)
  | truth | falsity => trivial
  | neg body ih => exact ih below
  | conj l r il ir | disj l r il ir | implies l r il ir =>
    simp only [FormulaBelow] at below
    exact ⟨il below.1, ir below.2⟩
  | all id body ih | ex id body ih =>
    by_cases same : id = binder
    · simpa [substitute, same, FormulaBelow] using below
    · simpa [substitute, same, FormulaBelow] using ih below

theorem skolem_term_below (fresh : Nat) (universals : List Nat) :
    TermBelow (fresh + 1) (.app fresh (universals.map Term.var)) := by
  simp only [TermBelow]
  refine ⟨by omega, ?_⟩
  intro term member
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp member
  simp [TermBelow]

theorem preservesBelow_mono {D : Type} {low high : Nat} {original extended : Interpretation D}
    (le : low ≤ high) (preserves : PreservesBelow high original extended) :
    PreservesBelow low original extended :=
  ⟨fun symbol below arguments => preserves.1 symbol (by omega) arguments, preserves.2⟩

theorem preservesBelow_trans {D : Type} {limit : Nat} {original middle final : Interpretation D}
    (first : PreservesBelow limit original middle) (second : PreservesBelow limit middle final) :
    PreservesBelow limit original final :=
  ⟨fun symbol below arguments => (second.1 symbol below arguments).trans (first.1 symbol below arguments),
    fun predicate arguments => (second.2 predicate arguments).trans (first.2 predicate arguments)⟩

end Fang.QuantifiedFOF.Skolem
