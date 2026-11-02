/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EqualityQuantifiedInput

namespace Fang.QuantifiedEqualityFrontend
open NamedQuantifiedEquality

mutual
theorem termWithin_correct (bound : List String) (term : Source.Term) :
    termWithin bound term = true ↔ NamedQuantified.TermWithin bound term := by
  cases term with
  | var name => simp [termWithin, NamedQuantified.TermWithin]
  | app fn args =>
    simp only [termWithin, NamedQuantified.TermWithin]
    exact termsWithin_correct bound args

theorem termsWithin_correct (bound : List String) (terms : List Source.Term) :
    termsWithin bound terms = true ↔ ∀ term ∈ terms, NamedQuantified.TermWithin bound term := by
  cases terms with
  | nil => simp [termsWithin]
  | cons term rest =>
    simp only [termsWithin, Bool.and_eq_true, termWithin_correct, termsWithin_correct,
      List.forall_mem_cons]
end

theorem atomWithin_correct (bound : List String) (value : NamedQuantifiedEquality.Atom) :
    atomWithin bound value = true ↔ value.Within bound := by
  cases value with
  | predicate name arguments => exact termsWithin_correct bound arguments
  | equal left right =>
    simp only [atomWithin, NamedQuantifiedEquality.Atom.Within, Bool.and_eq_true, termWithin_correct]

theorem formulaWithin_correct (bound : List String) (value : Formula) :
    formulaWithin bound value = true ↔ value.Within bound := by
  induction value generalizing bound with
  | atom value => exact atomWithin_correct bound value
  | truth => simp [formulaWithin, Formula.Within]
  | falsity => simp [formulaWithin, Formula.Within]
  | neg body ih => exact ih bound
  | conj left right il ir | disj left right il ir | implies left right il ir =>
    simp only [formulaWithin, Formula.Within, Bool.and_eq_true, il, ir]
  | all name body ih | ex name body ih => exact ih (name :: bound)

end Fang.QuantifiedEqualityFrontend
