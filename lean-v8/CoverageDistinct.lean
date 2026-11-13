/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Distinct objects as generated pairwise disequalities over the accepted
   numeric semantics. Independent Lean model; no Rust correspondence. -/
import ExpandedSource

namespace Fang.TptpCandidate.FullFof.Coverage

open Fang.TptpCandidate.FullFof.Integration (NumericDeclaration NumericInput)

/-- Pairs `(i, j)` of list positions with `i` before `j`, in lexicographic order. -/
def pairs : List Nat → List (Nat × Nat)
  | [] => []
  | first :: rest => rest.map (fun other => (first, other)) ++ pairs rest

/-- The CNF clause `left != right`, with equality at predicate slot `slot`. -/
def disequality (slot left right : Nat) : NumericDeclaration :=
  .cnf [⟨false, ⟨slot, [.app left [], .app right []]⟩⟩]

def distinctAxioms (slot : Nat) (objects : List Nat) : List NumericDeclaration :=
  (pairs objects).map (fun pair => disequality slot pair.1 pair.2)

/-- Different distinct objects denote different elements. They may still
    equal ordinary constants. -/
def Separated {D : Type} (model : Fang.Interpretation D) (objects : List Nat) : Prop :=
  ∀ left ∈ objects, ∀ right ∈ objects, left ≠ right →
    model.function left [] ≠ model.function right []

/-- Satisfiability under the TPTP distinct-object reading, with the reserved
    slot interpreted as equality exactly as in `NumericInput.Satisfiable`. -/
def DistinctSatisfiable (slot : Nat) (declarations : List NumericDeclaration)
    (objects : List Nat) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
    Separated model objects ∧ NamedQuantified.NumericModels (reserve slot model) declarations

def ReservedSatisfiable (slot : Nat) (declarations : List NumericDeclaration) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
    NamedQuantified.NumericModels (reserve slot model) declarations

theorem input_satisfiable (input : NumericInput) :
    input.Satisfiable ↔ ReservedSatisfiable input.predicates.length input.declarations :=
  Iff.rfl

theorem pairs_mem {objects : List Nat} {left right : Nat}
    (member : (left, right) ∈ pairs objects) :
    left ∈ objects ∧ right ∈ objects ∧ (objects.Nodup → left ≠ right) := by
  induction objects with
  | nil => simp [pairs] at member
  | cons first rest ih =>
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq] at member
    rcases member with ⟨other, present, same, rfl⟩ | member
    · subst same
      refine ⟨by simp, by simp [present], ?_⟩
      intro nodup equal
      subst equal
      exact (List.nodup_cons.mp nodup).1 present
    · have ⟨l, r, distinct⟩ := ih member
      exact ⟨by simp [l], by simp [r], fun nodup => distinct (List.nodup_cons.mp nodup).2⟩

theorem pairs_complete {objects : List Nat} (nodup : objects.Nodup) {left right : Nat}
    (l : left ∈ objects) (r : right ∈ objects) (distinct : left ≠ right) :
    (left, right) ∈ pairs objects ∨ (right, left) ∈ pairs objects := by
  induction objects with
  | nil => simp at l
  | cons first rest ih =>
    have restNodup := (List.nodup_cons.mp nodup).2
    simp only [pairs, List.mem_append, List.mem_map, Prod.mk.injEq]
    simp only [List.mem_cons] at l r
    rcases l with rfl | l
    · rcases r with rfl | r
      · exact absurd rfl distinct
      · exact .inl (.inl ⟨right, r, rfl, rfl⟩)
    · rcases r with rfl | r
      · exact .inr (.inl ⟨left, l, rfl, rfl⟩)
      · rcases ih restNodup l r with found | found
        · exact .inl (.inr found)
        · exact .inr (.inr found)

/-- Twice the number of generated clauses is `n * n - n`. -/
theorem pairs_length (objects : List Nat) :
    (pairs objects).length + (pairs objects).length + objects.length =
      objects.length * objects.length := by
  induction objects with
  | nil => rfl
  | cons first rest ih =>
    simp only [pairs, List.length_append, List.length_map, List.length_cons,
      Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    generalize rest.length * rest.length = square at ih ⊢
    omega

theorem distinctAxioms_length (slot : Nat) (objects : List Nat) :
    (distinctAxioms slot objects).length = (pairs objects).length := by
  simp [distinctAxioms]

theorem disequality_models {D : Type} [Nonempty D] (model : Fang.Interpretation D)
    (slot left right : Nat) :
    (disequality slot left right).Models (reserve slot model) ↔
      model.function left [] ≠ model.function right [] := by
  have valuation : Nonempty (Nat → D) := ⟨fun _ => Classical.choice inferInstance⟩
  simp [disequality, NamedQuantified.NumericDeclaration.Models, Fang.Clause.Valid,
    Fang.Clause.Holds, Fang.Literal.Holds, Fang.Atom.Holds, reserve, Fang.Term.eval]

/-- Equisatisfiability of the distinct-object reading and the generated axioms. -/
theorem distinct_satisfiable_iff (slot : Nat) (declarations : List NumericDeclaration)
    {objects : List Nat} (nodup : objects.Nodup) :
    DistinctSatisfiable slot declarations objects ↔
      ReservedSatisfiable slot (declarations ++ distinctAxioms slot objects) := by
  constructor
  · rintro ⟨D, inhabited, model, separated, holds⟩
    refine ⟨D, inhabited, model, ?_⟩
    intro declaration member
    rcases List.mem_append.mp member with original | generated
    · exact holds declaration original
    · simp only [distinctAxioms, List.mem_map] at generated
      rcases generated with ⟨⟨left, right⟩, present, rfl⟩
      have ⟨l, r, distinct⟩ := pairs_mem present
      exact (disequality_models model slot left right).mpr
        (separated left l right r (distinct nodup))
  · rintro ⟨D, inhabited, model, holds⟩
    refine ⟨D, inhabited, model, ?_, fun declaration member =>
      holds declaration (List.mem_append_left _ member)⟩
    intro left l right r distinct
    have generated (a b : Nat) (present : (a, b) ∈ pairs objects) :
        model.function a [] ≠ model.function b [] :=
      (disequality_models model slot a b).mp
        (holds _ (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b), present, rfl⟩)))
    rcases pairs_complete nodup l r distinct with found | found
    · exact generated left right found
    · exact fun equal => generated right left found equal.symm

/-- An empty or singleton inventory adds nothing and constrains nothing. -/
theorem distinct_trivial (slot : Nat) (declarations : List NumericDeclaration)
    {objects : List Nat} (small : objects.length ≤ 1) :
    DistinctSatisfiable slot declarations objects ↔ ReservedSatisfiable slot declarations := by
  constructor
  · rintro ⟨D, inhabited, model, _, holds⟩
    exact ⟨D, inhabited, model, holds⟩
  · rintro ⟨D, inhabited, model, holds⟩
    refine ⟨D, inhabited, model, ?_, holds⟩
    intro left l right r distinct
    match objects, small with
    | [], _ => simp at l
    | [only], _ =>
      simp only [List.mem_singleton] at l r
      exact absurd (l.trans r.symm) distinct

/-- Refuting the generated problem refutes the distinct-object reading. -/
theorem distinct_unsat (slot : Nat) (declarations : List NumericDeclaration)
    {objects : List Nat} (nodup : objects.Nodup)
    (refuted : ¬ ReservedSatisfiable slot (declarations ++ distinctAxioms slot objects)) :
    ¬ DistinctSatisfiable slot declarations objects :=
  fun model => refuted ((distinct_satisfiable_iff slot declarations nodup).mp model)

#print axioms Fang.TptpCandidate.FullFof.Coverage.input_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Coverage.pairs_mem
#print axioms Fang.TptpCandidate.FullFof.Coverage.pairs_complete
#print axioms Fang.TptpCandidate.FullFof.Coverage.pairs_length
#print axioms Fang.TptpCandidate.FullFof.Coverage.distinctAxioms_length
#print axioms Fang.TptpCandidate.FullFof.Coverage.disequality_models
#print axioms Fang.TptpCandidate.FullFof.Coverage.distinct_satisfiable_iff
#print axioms Fang.TptpCandidate.FullFof.Coverage.distinct_trivial
#print axioms Fang.TptpCandidate.FullFof.Coverage.distinct_unsat

end Fang.TptpCandidate.FullFof.Coverage
