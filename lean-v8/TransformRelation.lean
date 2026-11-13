/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Scope and binder preservation for the independent Skolem relation. -/
import UniversalPrefix
import TransformScope
import RecursiveExtension

namespace FangSkolemCore
open Fang.QuantifiedFOF

/-- The relation removes existential binders but keeps every surviving binder
    in its original structural position. This list ignores term contents. -/
def formulaBinders : Formula → List Nat
  | .atom _ | .truth | .falsity => []
  | .neg body => formulaBinders body
  | .conj left right | .disj left right | .implies left right =>
      formulaBinders left ++ formulaBinders right
  | .all id body | .ex id body => id :: formulaBinders body

theorem substituted_formula_binders (binder : Nat) (replacement : Fang.Term)
    (formula : Formula) :
    formulaBinders (Skolem.substitute binder replacement formula) = formulaBinders formula := by
  induction formula with
  | atom | truth | falsity => rfl
  | neg body ih => exact ih
  | conj left right il ir | disj left right il ir | implies left right il ir =>
    simp only [Skolem.substitute, formulaBinders, il, ir]
  | all id body ih | ex id body ih =>
    by_cases same : id = binder <;> simp only [Skolem.substitute, same, ite_true, ite_false, formulaBinders, ih]

theorem decoded_nnf_binders (formula : fang_skolem_core.fang_quantified_fof_core.Nnf) :
    formulaBinders (decodeNnf formula) = (nnfBinders formula).map (fun id => id.val) := by
  induction formula with
  | Literal literal =>
    simp only [decodeNnf, literalFormula]
    cases literal.positive <;> rfl
  | True | False => rfl
  | And left right il ir | Or left right il ir =>
    simp only [decodeNnf, nnfBinders, formulaBinders, List.map_append, il, ir]
  | Forall id body ih | Exists id body ih =>
    simp only [decodeNnf, nnfBinders, formulaBinders, List.map_cons, ih]

theorem skolemized_within {universals first source target last}
    (converted : Skolem.Skolemized universals first source target last)
    (within : source.Within universals) : target.Within universals := by
  induction converted with
  | atom | truth | falsity => exact within
  | negation child ih => exact ih within
  | conjunction left right il ir | disjunction left right il ir | implication left right il ir =>
    exact ⟨il within.1, ir within.2⟩
  | @universal universals first last id body target child ih =>
    have bodyWithin : body.Within (universals ++ [id]) :=
      formulaWithin_weaken (by
        intro other member
        simpa [List.mem_cons, List.mem_append, List.mem_singleton, or_comm] using member) body within
    exact formulaWithin_weaken (by
      intro other member
      simpa [List.mem_cons, List.mem_append, List.mem_singleton, or_comm] using member) target (ih bodyWithin)
  | @existential universals first last id body target bodyScope safe child ih =>
    apply ih
    apply formula_substitution_within id universals _ body _ bodyScope
    simp only [TermWithin]
    intro term member
    obtain ⟨variableId, present, rfl⟩ := List.mem_map.mp member
    simpa only [TermWithin] using present

theorem skolemized_binders {universals first source target last}
    (converted : Skolem.Skolemized universals first source target last) :
    (formulaBinders target).Sublist (formulaBinders source) := by
  induction converted with
  | atom | truth | falsity => exact .refl _
  | negation child ih => exact ih
  | conjunction left right il ir | disjunction left right il ir | implication left right il ir =>
    exact il.append ir
  | universal child ih => exact .cons_cons _ ih
  | @existential universals first last id body target within safe child ih =>
    rw [substituted_formula_binders] at ih
    exact .cons _ ih

end FangSkolemCore
