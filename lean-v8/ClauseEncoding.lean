/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Decoding

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityBridge
open fang_fof_equality_bridge

abbrev InputLiteral := fang_equality_inference_core.Literal
abbrev OutputLiteral := fang.syntax.Literal

attribute [local implicit_reducible] alloc.vec.into_iter.IntoIter
attribute [local implicit_reducible] alloc.vec.Vec.val Slice.val

def LiteralValid (value : Reservation) (literal : InputLiteral) : Prop :=
  match literal.atom with
  | .Predicate predicate arguments =>
      OrdinaryAnswer value predicate (alloc.vec.Vec.len arguments) = .Ok ()
  | .Equal _ _ => True

def EncodesLiteral (value : Reservation) (source : InputLiteral) (target : OutputLiteral) : Prop :=
  target.positive = source.positive ∧
  match source.atom with
  | .Predicate predicate arguments =>
      LiteralValid value source ∧ target.predicate = predicate ∧ target.arguments = arguments
  | .Equal left right => target.predicate = value.equality ∧ target.arguments.val = [left, right]

theorem encode_valid_spec (value : Reservation) (source : InputLiteral)
    (valid : LiteralValid value source) :
    Reservation.encode_literal value source ⦃ fun answer => ∃ target,
      answer = .Ok target ∧ EncodesLiteral value source target ⦄ := by
  cases source with
  | mk positive atom =>
    cases atom with
    | Predicate predicate arguments =>
      apply spec_mono (encode_predicate_spec value positive predicate arguments valid)
      intro answer same
      subst answer
      exact ⟨_, rfl, rfl, valid, rfl, rfl⟩
    | Equal left right =>
      apply spec_mono (encode_equality_spec value positive left right)
      intro answer result
      obtain ⟨arguments, rfl, shape⟩ := result
      exact ⟨_, rfl, rfl, rfl, shape⟩

theorem decode_encoded_spec (value : Reservation) (source : InputLiteral) (target : OutputLiteral)
    (reservation : ValidReservation value) (encoded : EncodesLiteral value source target) :
    Reservation.decode_literal value target ⦃ fun answer => answer = .Ok source ⦄ := by
  cases source with
  | mk positive atom =>
    cases target with
    | mk targetPositive targetPredicate targetArguments =>
      obtain ⟨samePositive, body⟩ := encoded
      dsimp only at samePositive
      subst targetPositive
      cases atom with
      | Predicate predicate arguments =>
        obtain ⟨valid, rfl, rfl⟩ := body
        exact decode_predicate_spec value positive _ _ reservation valid
      | Equal left right =>
        obtain ⟨rfl, shape⟩ := body
        exact decode_equality_spec value positive targetArguments left right shape

theorem iterator_next_nil {T : Type} (iter : alloc.vec.into_iter.IntoIter T)
    (empty : iter.val = []) :
    alloc.vec.into_iter.IteratorIntoIter.next iter = ok (none, iter) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rfl
  · rename_i head tail nonempty
    simp [empty] at nonempty

/-- The actual loop appends one conversion per input, in order. Its length
    premise justifies Vec pushes in the extracted model, not native allocation. -/
theorem encode_clause_loop_spec (iter : alloc.vec.into_iter.IntoIter InputLiteral)
    (value : Reservation) (result : alloc.vec.Vec OutputLiteral)
    (capacity : result.val.length + iter.val.length ≤ Usize.max)
    (valid : ∀ literal ∈ iter.val, LiteralValid value literal) :
    Reservation.encode_clause_loop iter value result ⦃ fun answer => ∃ output tail,
      answer = .Ok output ∧ output.val = result.val ++ tail ∧
      List.Forall₂ (EncodesLiteral value) iter.val tail ⦄ := by
  with_unfolding_all
    cases iter with
    | mk slice =>
      rw [Reservation.encode_clause_loop.eq_def]
      cases remaining : slice.val with
      | nil =>
        rw [iterator_next_nil _ remaining]
        simp [alloc.vec.Vec.val, Aeneas.Std.uncurry, remaining]
      | cons literal rest =>
        obtain ⟨restBound, nextEq⟩ := iterator_next_cons _ literal rest remaining
        rw [nextEq]
        simp only [bind_ok, Aeneas.Std.uncurry]
        have literalValid : LiteralValid value literal := valid literal (by
          change literal ∈ slice.val
          rw [remaining]
          exact List.mem_cons_self)
        apply spec_bind (encode_valid_spec value literal literalValid)
        intro answer encoded
        obtain ⟨target, rfl, relation⟩ := encoded
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        apply spec_bind (alloc.vec.Vec.push_spec result target (by
          change result.val.length + slice.val.length ≤ Usize.max at capacity
          rw [remaining] at capacity
          simp only [List.length_cons] at capacity
          omega))
        intro extended extendedEq
        apply spec_mono (encode_clause_loop_spec _ value extended (by
          simp only [alloc.vec.Vec.from_val]
          rw [extendedEq, List.length_append]
          change result.val.length + slice.val.length ≤ Usize.max at capacity
          rw [remaining] at capacity
          simp only [List.length_cons, List.length_nil] at capacity ⊢
          omega) (by
          intro item member
          apply valid item
          change item ∈ slice.val
          rw [remaining]
          exact List.mem_cons_of_mem _ (by simpa only [alloc.vec.Vec.from_val] using member)))
        intro answer encodedRest
        obtain ⟨output, tail, rfl, outputEq, restRelation⟩ := encodedRest
        refine ⟨output, target :: tail, rfl, ?_, ?_⟩
        · rw [outputEq, extendedEq, List.append_assoc]
          rfl
        · change List.Forall₂ (EncodesLiteral value) slice.val (target :: tail)
          rw [remaining]
          exact List.Forall₂.cons relation (by simpa only [alloc.vec.Vec.from_val] using restRelation)
termination_by iter.val.length
decreasing_by
  subst iter
  change (alloc.vec.Vec.from rest restBound).val.length < slice.val.length
  rw [alloc.vec.Vec.from_val, remaining]
  simp

theorem encode_clause_spec (value : Reservation) (clause : alloc.vec.Vec InputLiteral)
    (maximum : Usize) (fits : clause.val.length ≤ maximum.val)
    (valid : ∀ literal ∈ clause.val, LiteralValid value literal) :
    Reservation.encode_clause value clause maximum ⦃ fun answer => ∃ output,
      answer = .Ok output ∧ List.Forall₂ (EncodesLiteral value) clause.val output.val ⦄ := by
  have within : ¬ alloc.vec.Vec.len clause > maximum := by scalar_tac
  simp only [Reservation.encode_clause, within, ↓reduceIte,
    alloc.vec.IntoIteratorVec.into_iter, bind_ok]
  apply spec_mono (encode_clause_loop_spec clause value (alloc.vec.Vec.new OutputLiteral)
    (by simp) valid)
  intro answer encoded
  obtain ⟨output, tail, rfl, exactTail, relation⟩ := encoded
  change output.val = [] ++ tail at exactTail
  exact ⟨output, rfl, exactTail.symm ▸ relation⟩

end FangEqualityBridge
