/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Equality
import Fang.Checker

namespace Fang.Equality

/-- Internal bridge to the existing resolution/factoring checker, with equality interpreted explicitly. -/
def toBaseAtom : Atom → Fang.Atom
  | .predicate atom => ⟨atom.pred + 1, atom.args⟩
  | .equal left right => ⟨0, [left, right]⟩

def toBaseLiteral (literal : Literal) : Fang.Literal := ⟨literal.positive, toBaseAtom literal.atom⟩
def toBaseClause (clause : Clause) : Fang.Clause := clause.map toBaseLiteral

def baseInterpretation {D : Type} (model : Interpretation D) : Interpretation D where
  function := model.function
  predicate := fun symbol args => match symbol, args with
    | 0, [left, right] => left = right
    | 0, _ => False
    | index + 1, arguments => model.predicate index arguments

theorem eval_base {D : Type} (model : Interpretation D) (valuation : Nat → D) (term : Term) :
    term.eval (baseInterpretation model) valuation = term.eval model valuation := by
  cases term with
  | var varId => simp [Term.eval]
  | app symbol arguments =>
    simp only [Term.eval, baseInterpretation]
    congr 1
    exact List.map_congr_left fun term _ => eval_base model valuation term
termination_by sizeOf term

theorem literal_base {D : Type} (model : Interpretation D) (valuation : Nat → D) (literal : Literal) :
    (toBaseLiteral literal).Holds (baseInterpretation model) valuation ↔ literal.Holds model valuation := by
  cases literal with
  | mk positive atom =>
    have functions : Term.eval (baseInterpretation model) valuation = Term.eval model valuation :=
      funext (eval_base model valuation)
    cases atom <;> simp only [toBaseLiteral, toBaseAtom, Fang.Literal.Holds, Fang.Atom.Holds,
      Literal.Holds, Atom.Holds, functions] <;> rfl

theorem clause_base {D : Type} (model : Interpretation D) (clause : Clause) :
    (toBaseClause clause).Valid (baseInterpretation model) ↔ clauseValid model clause := by
  constructor
  · intro valid valuation
    obtain ⟨literal, member, holds⟩ := valid valuation
    change literal ∈ clause.map toBaseLiteral at member
    obtain ⟨original, originalMember, same⟩ := List.mem_map.mp member
    rw [← same] at holds
    exact ⟨original, originalMember, (literal_base model valuation original).mp holds⟩
  · intro valid valuation
    obtain ⟨literal, member, holds⟩ := valid valuation
    exact ⟨toBaseLiteral literal, List.mem_map.mpr ⟨literal, member, rfl⟩,
      (literal_base model valuation literal).mpr holds⟩

/-- Uses the production checker's substitution uniqueness and exact pivot conditions. -/
def checkFactor (premise : Clause) (first second : Nat) (substitution : Subst) (claimed : Clause) : Option Clause :=
  if Fang.factor (toBaseClause premise) first second substitution = some (toBaseClause claimed) then some claimed else none

theorem checkFactor_sound {D : Type} (model : Interpretation D) (premise claimed output : Clause)
    (first second : Nat) (substitution : Subst) (valid : clauseValid model premise)
    (accepted : checkFactor premise first second substitution claimed = some output) : clauseValid model output := by
  unfold checkFactor at accepted
  split at accepted
  next checked =>
    cases accepted
    exact (clause_base model claimed).mp
      (Fang.factor_valid (baseInterpretation model) _ _ first second substitution ((clause_base model premise).mpr valid) checked)
  next rejected => contradiction

/-- The existing checker applies disjoint even/odd renamings before the simultaneous witness. -/
def checkResolution (left right : Clause) (leftPosition rightPosition : Nat)
    (substitution : Subst) (claimed : Clause) : Option Clause :=
  if Fang.resolve (toBaseClause left) leftPosition (toBaseClause right) rightPosition substitution =
      some (toBaseClause claimed) then some claimed else none

theorem checkResolution_sound {D : Type} (model : Interpretation D) (left right claimed output : Clause)
    (leftPosition rightPosition : Nat) (substitution : Subst)
    (leftValid : clauseValid model left) (rightValid : clauseValid model right)
    (accepted : checkResolution left right leftPosition rightPosition substitution claimed = some output) :
    clauseValid model output := by
  unfold checkResolution at accepted
  split at accepted
  next checked =>
    cases accepted
    exact (clause_base model claimed).mp
      (Fang.resolve_valid (baseInterpretation model) _ _ _ leftPosition rightPosition substitution
        ((clause_base model left).mpr leftValid) ((clause_base model right).mpr rightValid) checked)
  next rejected => contradiction

end Fang.Equality
