/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent mathematical specification. Generated-code refinement is separate. -/
import Equality
import SkolemModel

namespace Fang.EqualityBridge

def reserveInterpretation {D : Type} (reserved : Nat) (model : Interpretation D) :
    Interpretation D where
  function := model.function
  predicate symbol arguments :=
    if symbol = reserved then
      match arguments with
      | [left, right] => left = right
      | _ => False
    else model.predicate symbol arguments

def AtomEligible (reserved : Nat) : Equality.Atom → Prop
  | .predicate atom => atom.pred < reserved
  | .equal _ _ => True

def encodeAtom (reserved : Nat) : Equality.Atom → Atom
  | .predicate atom => atom
  | .equal left right => ⟨reserved, [left, right]⟩

def encodeLiteral (reserved : Nat) (literal : Equality.Literal) : Literal :=
  ⟨literal.positive, encodeAtom reserved literal.atom⟩

theorem term_eval_reserved {D : Type} (reserved : Nat) (model : Interpretation D)
    (valuation : Nat → D) (term : Term) :
    term.eval (reserveInterpretation reserved model) valuation = term.eval model valuation := by
  cases term with
  | var id => simp [Term.eval]
  | app symbol arguments =>
    simp only [Term.eval, reserveInterpretation]
    congr 1
    apply List.map_congr_left
    intro term member
    exact term_eval_reserved reserved model valuation term
termination_by sizeOf term

theorem atom_encoding_holds {D : Type} (reserved : Nat) (model : Interpretation D)
    (valuation : Nat → D) (atom : Equality.Atom) (eligible : AtomEligible reserved atom) :
    (encodeAtom reserved atom).Holds (reserveInterpretation reserved model) valuation ↔
      atom.Holds model valuation := by
  have evaluation : Term.eval (reserveInterpretation reserved model) valuation =
      Term.eval model valuation := funext (term_eval_reserved reserved model valuation)
  cases atom with
  | predicate atom =>
    have different : atom.pred ≠ reserved := by unfold AtomEligible at eligible; omega
    simp only [encodeAtom, Atom.Holds, Equality.Atom.Holds, evaluation]
    simp [reserveInterpretation, different]
  | equal left right =>
    simp only [encodeAtom, Atom.Holds, Equality.Atom.Holds, evaluation]
    simp [reserveInterpretation]

theorem literal_encoding_holds {D : Type} (reserved : Nat) (model : Interpretation D)
    (valuation : Nat → D) (literal : Equality.Literal)
    (eligible : AtomEligible reserved literal.atom) :
    (encodeLiteral reserved literal).Holds (reserveInterpretation reserved model) valuation ↔
      literal.Holds model valuation := by
  cases positive : literal.positive <;>
    simp [encodeLiteral, Literal.Holds, Equality.Literal.Holds, positive,
      atom_encoding_holds reserved model valuation literal.atom eligible]

theorem clause_encoding_holds {D : Type} (reserved : Nat) (model : Interpretation D)
    (valuation : Nat → D) (clause : Equality.Clause)
    (eligible : ∀ literal ∈ clause, AtomEligible reserved literal.atom) :
    Clause.Holds (reserveInterpretation reserved model) valuation (clause.map (encodeLiteral reserved)) ↔
      Equality.clauseHolds model valuation clause := by
  constructor
  · rintro ⟨encoded, member, holds⟩
    obtain ⟨literal, sourceMember, rfl⟩ := List.mem_map.mp member
    exact ⟨literal, sourceMember, (literal_encoding_holds reserved model valuation literal
      (eligible literal sourceMember)).mp holds⟩
  · rintro ⟨literal, member, holds⟩
    exact ⟨encodeLiteral reserved literal, List.mem_map.mpr ⟨literal, member, rfl⟩,
      (literal_encoding_holds reserved model valuation literal (eligible literal member)).mpr holds⟩

theorem clause_encoding_valid {D : Type} (reserved : Nat) (model : Interpretation D)
    (clause : Equality.Clause) (eligible : ∀ literal ∈ clause, AtomEligible reserved literal.atom) :
    Clause.Valid (reserveInterpretation reserved model) (clause.map (encodeLiteral reserved)) ↔
      Equality.clauseValid model clause :=
  forall_congr' (fun valuation => clause_encoding_holds reserved model valuation clause eligible)

/-- Recover built-in equality with the extended functions and original ordinary
    predicates. Functions may change outside the separately reserved range. -/
def recoverInterpretation {D : Type} (original extended : Interpretation D) : Interpretation D where
  function := extended.function
  predicate := original.predicate

theorem recover_reserved {D : Type} (reserved : Nat) (original extended : Interpretation D)
    (preserved : ∀ symbol arguments,
      extended.predicate symbol arguments =
        (reserveInterpretation reserved original).predicate symbol arguments) :
    reserveInterpretation reserved (recoverInterpretation original extended) = extended := by
  cases extended with
  | mk functions predicates =>
    simp only [reserveInterpretation, recoverInterpretation]
    congr 1
    funext symbol arguments
    exact (preserved symbol arguments).symm

/-- The existing Skolem extension contract preserves the reserved equality
    interpretation, even though new functions alter term evaluation. -/
theorem skolem_extension_recovers {D : Type} (reserved functionLimit : Nat)
    (original extended : Interpretation D)
    (preserved : QuantifiedFOF.Skolem.PreservesBelow functionLimit
      (reserveInterpretation reserved original) extended) :
    reserveInterpretation reserved (recoverInterpretation original extended) = extended :=
  recover_reserved reserved original extended preserved.2

theorem extended_clause_conversion {D : Type} (reserved functionLimit : Nat)
    (original extended : Interpretation D) (clause : Equality.Clause)
    (eligible : ∀ literal ∈ clause, AtomEligible reserved literal.atom)
    (preserved : QuantifiedFOF.Skolem.PreservesBelow functionLimit
      (reserveInterpretation reserved original) extended) :
    Clause.Valid extended (clause.map (encodeLiteral reserved)) ↔
      Equality.clauseValid (recoverInterpretation original extended) clause := by
  have meaning := clause_encoding_valid reserved (recoverInterpretation original extended) clause eligible
  rw [skolem_extension_recovers reserved functionLimit original extended preserved] at meaning
  exact meaning

end Fang.EqualityBridge
