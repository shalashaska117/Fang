/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import InverseClause
import OrderedTrace

open Aeneas.Std

namespace FangQuantifiedEquality
open fang_fof_equality_bridge FangEqualityBridge

/-- One successful call to the extracted Rust decoder, with exact structural
    input and output representations. No clause or literal may be omitted. -/
def ActualClauseConversion (reservation : Reservation)
    (ordinary : Fang.Clause) (equality : Fang.Equality.Clause) : Prop :=
  ∃ (input : alloc.vec.Vec OutputLiteral) (output : alloc.vec.Vec InputLiteral)
      (maximum : Usize),
    Reservation.decode_clause reservation input maximum = .ok (.Ok output) ∧
    ordinary = input.val.map FangEqualityBridge.decodeOutput ∧
    equality = output.val.map FangEqualityBridge.decodeInput

/-- The whole ordered problem is converted. Repetition and empty clauses remain
    at their original positions; this relation does not deduplicate anything. -/
def ActualProblemConversion (reservation : Reservation)
    (ordinary : Fang.Problem) (equality : Fang.Equality.Problem) : Prop :=
  List.Forall₂ (ActualClauseConversion reservation) ordinary equality

theorem actualClause_literal_count {reservation ordinary equality}
    (converted : ActualClauseConversion reservation ordinary equality) :
    ordinary.length = equality.length := by
  obtain ⟨input, output, maximum, success, rfl, rfl⟩ := converted
  have exactOrder := FangEqualityBridge.decode_clause_inverse reservation input output maximum success
  simpa only [List.length_map] using exactOrder.length_eq.symm

theorem actualProblem_clause_count {reservation ordinary equality}
    (converted : ActualProblemConversion reservation ordinary equality) :
    ordinary.length = equality.length := converted.length_eq

theorem actualProblem_literal_counts {reservation ordinary equality}
    (converted : ActualProblemConversion reservation ordinary equality) :
    ordinary.map List.length = equality.map List.length := by
  induction converted with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, actualClause_literal_count head, ih]

theorem actualClause_meaning {D : Type} (original extended : Fang.Interpretation D)
    (reservation : Reservation) (functionLimit : Nat)
    (valid : FangEqualityBridge.ValidReservation reservation)
    (preserved : Fang.QuantifiedFOF.Skolem.PreservesBelow functionLimit
      (Fang.EqualityBridge.reserveInterpretation reservation.equality.val original) extended)
    {ordinary equality} (converted : ActualClauseConversion reservation ordinary equality) :
    (∀ literal ∈ equality,
      Fang.EqualityBridge.AtomEligible reservation.equality.val literal.atom) ∧
    (Fang.Clause.Valid extended ordinary ↔
      Fang.Equality.clauseValid
        (Fang.EqualityBridge.recoverInterpretation original extended) equality) := by
  obtain ⟨input, output, maximum, success, rfl, rfl⟩ := converted
  exact FangEqualityBridge.decode_clause_success_meaning original extended reservation input output
    maximum functionLimit valid preserved success

theorem actualProblem_eligible {D : Type} (original extended : Fang.Interpretation D)
    (reservation : Reservation) (functionLimit : Nat)
    (valid : FangEqualityBridge.ValidReservation reservation)
    (preserved : Fang.QuantifiedFOF.Skolem.PreservesBelow functionLimit
      (Fang.EqualityBridge.reserveInterpretation reservation.equality.val original) extended)
    {ordinary equality} (converted : ActualProblemConversion reservation ordinary equality) :
    ∀ clause ∈ equality, ∀ literal ∈ clause,
      Fang.EqualityBridge.AtomEligible reservation.equality.val literal.atom := by
  induction converted with
  | nil => simp
  | cons head tail ih =>
    intro clause member
    rcases List.mem_cons.mp member with rfl | member
    · exact (actualClause_meaning original extended reservation functionLimit valid preserved head).1
    · exact ih clause member

/-- The extended interpretation preserves every predicate, including reserved
    equality. The recovered equality model uses its extended function field. -/
theorem actualProblem_models {D : Type} (original extended : Fang.Interpretation D)
    (reservation : Reservation) (functionLimit : Nat)
    (valid : FangEqualityBridge.ValidReservation reservation)
    (preserved : Fang.QuantifiedFOF.Skolem.PreservesBelow functionLimit
      (Fang.EqualityBridge.reserveInterpretation reservation.equality.val original) extended)
    {ordinary equality} (converted : ActualProblemConversion reservation ordinary equality) :
    ordinary.Models extended ↔ Fang.Equality.models
      (Fang.EqualityBridge.recoverInterpretation original extended) equality := by
  induction converted with
  | nil => simp [Fang.Problem.Models, Fang.Equality.models]
  | cons head tail ih =>
    have clause := (actualClause_meaning original extended reservation functionLimit valid preserved head).2
    simpa only [Fang.Problem.Models, Fang.Equality.models, List.mem_cons, forall_eq_or_imp]
      using and_congr clause ih

end FangQuantifiedEquality
