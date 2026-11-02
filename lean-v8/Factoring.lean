/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Equality

namespace Fang.Equality

/-- The second positive equality remains in the residual clause. -/
theorem equality_factoring_sound {D : Type} (model : Interpretation D)
    (left right otherLeft otherRight : Term) (rest : Clause) (substitution : Subst)
    (premise : clauseValid model (⟨true, .equal left right⟩ :: rest))
    (retained : (⟨true, .equal otherLeft otherRight⟩ : Literal) ∈ rest)
    (equalized : left.subst substitution = otherLeft.subst substitution) :
    clauseValid model (⟨false, .equal (right.subst substitution) (otherRight.subst substitution)⟩ ::
      rest.map (Literal.subst substitution)) := by
  classical
  intro valuation
  rw [clause_cons_holds]
  by_cases remaining : clauseHolds model valuation (rest.map (Literal.subst substitution))
  · exact Or.inr remaining
  · left
    have source := clause_valid_subst model substitution _ premise valuation
    rw [List.map_cons, clause_cons_holds] at source
    have chosen := source.resolve_right remaining
    have retainedFalse : ¬ (Literal.subst substitution ⟨true, .equal otherLeft otherRight⟩).Holds model valuation := by
      intro holds
      exact remaining ⟨_, List.mem_map.mpr ⟨_, retained, rfl⟩, holds⟩
    simp only [Literal.subst, Atom.subst, Literal.Holds, Atom.Holds, Bool.false_eq_true,
      if_false, if_true] at chosen retainedFalse ⊢
    rw [equalized] at chosen
    intro rejected
    exact retainedFalse (chosen.trans rejected)

def checkEqualityFactoring (premise before after : Clause) (left right otherLeft otherRight : Term)
    (substitution : Subst) : Option Clause :=
  if premise = before ++ ⟨true, .equal left right⟩ :: after ∧
      (⟨true, .equal otherLeft otherRight⟩ : Literal) ∈ before ++ after ∧
      left.subst substitution = otherLeft.subst substitution then
    some (⟨false, .equal (right.subst substitution) (otherRight.subst substitution)⟩ ::
      (before ++ after).map (Literal.subst substitution))
  else none

theorem checkEqualityFactoring_sound {D : Type} (model : Interpretation D)
    (premise before after output : Clause) (left right otherLeft otherRight : Term) (substitution : Subst)
    (valid : clauseValid model premise)
    (accepted : checkEqualityFactoring premise before after left right otherLeft otherRight substitution = some output) :
    clauseValid model output := by
  unfold checkEqualityFactoring at accepted
  split at accepted
  next checked =>
    cases accepted
    rw [checked.1] at valid
    exact equality_factoring_sound model left right otherLeft otherRight (before ++ after) substitution
      (focus_valid model before after _ valid) checked.2.1 checked.2.2
  next rejected => contradiction

end Fang.Equality
