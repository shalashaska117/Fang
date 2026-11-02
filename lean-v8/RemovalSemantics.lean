/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Representation and same-interpretation link for the actual Rust erasure. -/
import RemovalPublic
import BinderSemantics

open Aeneas Aeneas.Std Aeneas.Std.WP Result Aeneas.Data.ListN
namespace FangBinderRemovalCore
open fang_binder_removal_core

mutual
def decodeTerm : fang.syntax.Term → Fang.Term
  | .Var id => .var id.val
  | .Fun symbol arguments => .app symbol.val (decodeVec arguments)
def decodeVec : alloc.vec.Vec fang.syntax.Term → List Fang.Term
  | ⟨slice⟩ => decodeSlice slice
def decodeSlice : Slice fang.syntax.Term → List Fang.Term
  | ⟨_, terms, _⟩ => decodeTerms terms
def decodeTerms {n : Nat} : ListN fang.syntax.Term n → List Fang.Term
  | .nil => []
  | .cons term rest => decodeTerm term :: decodeTerms rest
end

theorem decodeTerms_eq_map {n : Nat} (terms : ListN fang.syntax.Term n) :
    decodeTerms terms = terms.toList.map decodeTerm := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp [decodeTerms, ListN.toList, ih]

theorem decodeVec_eq_map (arguments : alloc.vec.Vec fang.syntax.Term) :
    decodeVec arguments = arguments.val.map decodeTerm := by
  cases arguments with
  | mk slice =>
    cases slice with
    | mk count terms bound =>
      simpa [decodeVec, decodeSlice, alloc.vec.Vec.val, Slice.val] using decodeTerms_eq_map terms

def decodeLiteral (literal : fang.syntax.Literal) : Fang.Literal :=
  ⟨literal.positive, literal.predicate.val, decodeVec literal.arguments⟩

def decodeInput : Input → Fang.QuantifiedFOF.Nnf
  | .Literal literal => .lit (decodeLiteral literal)
  | .True => .truth
  | .False => .falsity
  | .And left right => .conj (decodeInput left) (decodeInput right)
  | .Or left right => .disj (decodeInput left) (decodeInput right)
  | .Forall id body => .all id.val (decodeInput body)
  | .Exists id body => .ex id.val (decodeInput body)

def decodeOutput : Output → Fang.GroundFOF.Nnf
  | .Literal literal => .lit (decodeLiteral literal)
  | .True => .truth
  | .False => .falsity
  | .And left right => .conj (decodeOutput left) (decodeOutput right)
  | .Or left right => .disj (decodeOutput left) (decodeOutput right)

theorem erased_to_spec {source target} (erased : Erased source target) :
    Fang.QuantifiedFOF.BinderRemoval.Erases (decodeInput source) (decodeOutput target) := by
  induction erased with
  | literal value => exact .lit _
  | truth => exact .truth
  | falsity => exact .falsity
  | and_ a b ia ib => exact .conj ia ib
  | or_ a b ia ib => exact .disj ia ib
  | forall_ child ih => exact .all ih

theorem remove_universals_erases {source limits result}
    (success : remove_universals source limits = .ok (.Ok result)) :
    Fang.QuantifiedFOF.BinderRemoval.Erases (decodeInput source) (decodeOutput result.formula) :=
  erased_to_spec (remove_universals_success success).1

/-- The exact original literal list, including duplicates and term arguments. -/
theorem remove_universals_literals {source limits result}
    (success : remove_universals source limits = .ok (.Ok result)) :
    Fang.QuantifiedFOF.BinderRemoval.groundLiterals (decodeOutput result.formula) =
      Fang.QuantifiedFOF.BinderRemoval.literals (decodeInput source) :=
  (remove_universals_erases success).literals

/-- Same full interpretation, with scope and rectification supplied explicitly. -/
theorem remove_universals_models {D : Type} [Nonempty D] (model : Fang.Interpretation D)
    {source limits result} (success : remove_universals source limits = .ok (.Ok result))
    (free : List Nat) (safe : Fang.QuantifiedFOF.BinderRemoval.RectifiedWithin free (decodeInput source)) :
    (∀ valuation, (decodeInput source).Holds model valuation) ↔
      ∀ valuation, (decodeOutput result.formula).Holds model valuation :=
  (remove_universals_erases success).universal_closure model free safe

/-- Composition with the existing mathematical ordered clausifier. This does
    not claim that the executable Rust clausifier is connected at this boundary. -/
theorem remove_universals_clause_models {D : Type} [Nonempty D] (model : Fang.Interpretation D)
    {source limits result} (success : remove_universals source limits = .ok (.Ok result))
    (free : List Nat) (safe : Fang.QuantifiedFOF.BinderRemoval.RectifiedWithin free (decodeInput source)) :
    (decodeOutput result.formula).clauses.Models model ↔
      ∀ valuation, (decodeInput source).Holds model valuation :=
  (remove_universals_erases success).clause_models model free safe

end FangBinderRemovalCore
