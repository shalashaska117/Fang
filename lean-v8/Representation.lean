/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Structural decoders only. The conversion algorithms remain generated Rust. -/
import ClauseDecoding
import SemanticModel

namespace FangEqualityBridge
open Aeneas.Std Aeneas.Data.ListN fang_fof_equality_bridge

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

theorem decodeTerms_map {n : Nat} (terms : ListN fang.syntax.Term n) :
    decodeTerms terms = terms.toList.map decodeTerm := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp only [decodeTerms, ListN.toList, List.map_cons, ih]

theorem decodeVec_map (arguments : alloc.vec.Vec fang.syntax.Term) :
    decodeVec arguments = arguments.val.map decodeTerm := by
  cases arguments with
  | mk slice =>
    cases slice with
    | mk n terms bound => exact decodeTerms_map terms

def decodeInputAtom : fang_equality_inference_core.Atom → Fang.Equality.Atom
  | .Predicate symbol arguments => .predicate ⟨symbol.val, decodeVec arguments⟩
  | .Equal left right => .equal (decodeTerm left) (decodeTerm right)

def decodeInput (literal : InputLiteral) : Fang.Equality.Literal :=
  ⟨literal.positive, decodeInputAtom literal.atom⟩

def decodeOutput (literal : OutputLiteral) : Fang.Literal :=
  ⟨literal.positive, ⟨literal.predicate.val, decodeVec literal.arguments⟩⟩

theorem encoded_literal_model (value : Reservation) (source : InputLiteral) (target : OutputLiteral)
    (reservation : ValidReservation value) (encoded : EncodesLiteral value source target) :
    Fang.EqualityBridge.AtomEligible value.equality.val (decodeInput source).atom ∧
    decodeOutput target = Fang.EqualityBridge.encodeLiteral value.equality.val (decodeInput source) := by
  cases source with
  | mk positive atom =>
    cases target with
    | mk targetPositive targetPredicate targetArguments =>
      obtain ⟨samePositive, body⟩ := encoded
      dsimp only at samePositive
      subst targetPositive
      cases atom with
      | Predicate predicate arguments =>
        obtain ⟨valid, headEq, argumentsEq⟩ := body
        change targetPredicate = predicate at headEq
        change targetArguments = arguments at argumentsEq
        have below : predicate.val < value.original_predicates.val.length := by
          change OrdinaryAnswer value predicate (alloc.vec.Vec.len arguments) = .Ok () at valid
          unfold OrdinaryAnswer at valid
          split at valid
          · assumption
          · contradiction
        constructor
        · change predicate.val < value.equality.val
          rw [reservation]
          exact below
        · simp [decodeOutput, decodeInput, decodeInputAtom,
            Fang.EqualityBridge.encodeLiteral, Fang.EqualityBridge.encodeAtom, headEq, argumentsEq]
      | Equal left right =>
        obtain ⟨headEq, shape⟩ := body
        change targetPredicate = value.equality at headEq
        change targetArguments.val = [left, right] at shape
        constructor
        · trivial
        · simp [decodeOutput, decodeInput, decodeInputAtom,
            Fang.EqualityBridge.encodeLiteral, Fang.EqualityBridge.encodeAtom,
            headEq, decodeVec_map, shape]

theorem encoded_clause_model (value : Reservation) (source : List InputLiteral) (target : List OutputLiteral)
    (reservation : ValidReservation value) (encoded : List.Forall₂ (EncodesLiteral value) source target) :
    (∀ literal ∈ source.map decodeInput,
      Fang.EqualityBridge.AtomEligible value.equality.val literal.atom) ∧
    target.map decodeOutput = (source.map decodeInput).map
      (Fang.EqualityBridge.encodeLiteral value.equality.val) := by
  induction encoded with
  | nil => simp
  | @cons source target sources targets relation remainder ih =>
    obtain ⟨eligible, exactLiteral⟩ := encoded_literal_model value source target reservation relation
    constructor
    · intro literal member
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact eligible
      · exact ih.1 literal member
    · simp only [List.map_cons, exactLiteral, ih.2]

end FangEqualityBridge
