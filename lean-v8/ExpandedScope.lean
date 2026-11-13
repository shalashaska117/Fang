/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Scope transport for the existing numeric formula representation. -/
import ExpandedLiteral

namespace Fang.TptpCandidate.FullFof.Integration

theorem encoded_term_within (term : Source.Term) (functions : Arity.Table)
    (variables : Source.Variables) (bound : List String)
    (closed : NamedQuantified.TermWithin bound term) :
    QuantifiedFOF.TermWithin (bound.map variables.id) (Arity.encodeTerm functions variables term) := by
  cases term with
  | var name =>
    simp only [NamedQuantified.TermWithin] at closed
    simp only [Arity.encodeTerm, QuantifiedFOF.TermWithin]
    exact List.mem_map.mpr ⟨name, closed, rfl⟩
  | app name args =>
    simp only [NamedQuantified.TermWithin] at closed
    simp only [Arity.encodeTerm, QuantifiedFOF.TermWithin]
    intro value member
    obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
    exact encoded_term_within child functions variables bound (closed child present)
termination_by sizeOf term

theorem lowered_within {left right : QuantifiedFOF.Formula} {bound}
    (operator : Binary) (l : left.Within bound) (r : right.Within bound) :
    (operator.lower left right).Within bound := by
  cases operator <;> simp_all [Binary.lower, QuantifiedFOF.Formula.Within]

theorem encoded_formula_within (formula : Formula) (functions predicates : Arity.Table)
    (variables : Source.Variables) (bound : List String) (closed : formula.Within bound) :
    (formula.encode functions predicates variables).Within (bound.map variables.id) := by
  induction formula generalizing bound with
  | atom name args =>
    intro value member
    obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
    exact encoded_term_within child functions variables bound (closed child present)
  | equal left right =>
    simp only [Formula.encode, QuantifiedFOF.Formula.Within, List.mem_cons,
      List.not_mem_nil, or_false]
    intro value member
    rcases member with rfl | rfl
    · exact encoded_term_within left functions variables bound closed.1
    · exact encoded_term_within right functions variables bound closed.2
  | truth | falsity => trivial
  | neg body ih => exact ih bound closed
  | pair operator left right ihl ihr =>
    exact lowered_within operator (ihl bound closed.1) (ihr bound closed.2)
  | all name body ih => exact ih (name :: bound) closed
  | ex name body ih => exact ih (name :: bound) closed

#print axioms Fang.TptpCandidate.FullFof.Integration.encoded_term_within
#print axioms Fang.TptpCandidate.FullFof.Integration.lowered_within
#print axioms Fang.TptpCandidate.FullFof.Integration.encoded_formula_within

end Fang.TptpCandidate.FullFof.Integration
