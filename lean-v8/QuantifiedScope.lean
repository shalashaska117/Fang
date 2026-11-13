/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import QuantifiedInput

namespace Fang.QuantifiedFrontend

mutual
theorem termWithin_correct (bound : List Nat) (term : Term) :
    termWithin bound term = true ↔ QuantifiedFOF.TermWithin bound term := by
  cases term with
  | var id => simp [termWithin, QuantifiedFOF.TermWithin]
  | app fn args =>
    simp only [termWithin, QuantifiedFOF.TermWithin]
    exact termsWithin_correct bound args

theorem termsWithin_correct (bound : List Nat) (terms : List Term) :
    termsWithin bound terms = true ↔ ∀ term ∈ terms, QuantifiedFOF.TermWithin bound term := by
  cases terms with
  | nil => simp [termsWithin]
  | cons term rest =>
    simp only [termsWithin, Bool.and_eq_true, termWithin_correct, termsWithin_correct,
      List.forall_mem_cons]
end

theorem formulaWithin_correct (bound : List Nat) (formula : QuantifiedFOF.Formula) :
    formulaWithin bound formula = true ↔ formula.Within bound := by
  induction formula generalizing bound with
  | atom atom => exact termsWithin_correct bound atom.args
  | truth => simp [formulaWithin, QuantifiedFOF.Formula.Within]
  | falsity => simp [formulaWithin, QuantifiedFOF.Formula.Within]
  | neg body ih => exact ih bound
  | conj left right ihl ihr | disj left right ihl ihr | implies left right ihl ihr =>
    simp only [formulaWithin, QuantifiedFOF.Formula.Within, Bool.and_eq_true, ihl, ihr]
  | all id body ih | ex id body ih => exact ih (id :: bound)

end Fang.QuantifiedFrontend
