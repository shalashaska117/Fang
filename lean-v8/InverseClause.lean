/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import InverseLiteral
import Meaning

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityBridge
open fang_fof_equality_bridge

attribute [local implicit_reducible] alloc.vec.into_iter.IntoIter
attribute [local implicit_reducible] alloc.vec.Vec.val Slice.val

def InverseLoopPost (value : Reservation) (before : List InputLiteral) (input : List OutputLiteral)
    (answer : core.result.Result (alloc.vec.Vec InputLiteral) fang_fof_equality_bridge.Error) : Prop :=
  match answer with
  | .Ok output => ∃ tail, output.val = before ++ tail ∧ List.Forall₂ (EncodesLiteral value) tail input
  | .Err error => DecodeError error

theorem decode_clause_loop_inverse_spec (iter : alloc.vec.into_iter.IntoIter OutputLiteral)
    (value : Reservation) (result : alloc.vec.Vec InputLiteral)
    (capacity : result.val.length + iter.val.length ≤ Usize.max) :
    Reservation.decode_clause_loop iter value result
      ⦃ InverseLoopPost value result.val iter.val ⦄ := by
  with_unfolding_all
    cases iter with
    | mk slice =>
      rw [Reservation.decode_clause_loop.eq_def]
      cases remaining : slice.val with
      | nil =>
        rw [iterator_next_nil _ remaining]
        simp [alloc.vec.Vec.val, Aeneas.Std.uncurry, InverseLoopPost, remaining]
      | cons literal rest =>
        obtain ⟨restBound, nextEq⟩ := iterator_next_cons _ literal rest remaining
        rw [nextEq]
        simp only [bind_ok, Aeneas.Std.uncurry]
        apply spec_bind (decode_literal_inverse_spec value literal)
        intro answer decoded
        cases answer with
        | Err error =>
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            InverseLoopPost, DecodeLiteralPost] using decoded
        | Ok source =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          apply spec_bind (alloc.vec.Vec.push_spec result source (by
            change result.val.length + slice.val.length ≤ Usize.max at capacity
            rw [remaining] at capacity
            simp only [List.length_cons] at capacity
            omega))
          intro extended extendedEq
          apply spec_mono (decode_clause_loop_inverse_spec _ value extended (by
            simp only [alloc.vec.Vec.from_val]
            rw [extendedEq, List.length_append]
            change result.val.length + slice.val.length ≤ Usize.max at capacity
            rw [remaining] at capacity
            simp only [List.length_cons, List.length_nil] at capacity ⊢
            omega))
          intro answer inverse
          cases answer with
          | Err error => exact inverse
          | Ok output =>
            obtain ⟨tail, outputEq, relation⟩ := inverse
            refine ⟨source :: tail, ?_, ?_⟩
            · rw [outputEq, extendedEq, List.append_assoc]
              rfl
            · change List.Forall₂ (EncodesLiteral value) (source :: tail) slice.val
              rw [remaining]
              exact List.Forall₂.cons decoded
                (by simpa only [alloc.vec.Vec.from_val] using relation)
termination_by iter.val.length
decreasing_by
  subst iter
  change (alloc.vec.Vec.from rest restBound).val.length < slice.val.length
  rw [alloc.vec.Vec.from_val, remaining]
  simp

def InverseClausePost (value : Reservation) (input : List OutputLiteral)
    (answer : core.result.Result (alloc.vec.Vec InputLiteral) fang_fof_equality_bridge.Error) : Prop :=
  match answer with
  | .Ok output => List.Forall₂ (EncodesLiteral value) output.val input
  | .Err error => error = .LiteralLimit ∨ DecodeError error

/-- Actual decoding terminates with either an ordered representation witness
    or exactly one declared literal-cap/head/arity error. -/
theorem decode_clause_inverse_spec (value : Reservation) (input : alloc.vec.Vec OutputLiteral)
    (maximum : Usize) :
    Reservation.decode_clause value input maximum ⦃ InverseClausePost value input.val ⦄ := by
  unfold Reservation.decode_clause
  dsimp only
  split
  next full => simp [InverseClausePost]
  next available =>
    simp only [alloc.vec.IntoIteratorVec.into_iter, bind_ok]
    apply spec_mono (decode_clause_loop_inverse_spec input value (alloc.vec.Vec.new InputLiteral) (by simp))
    intro answer inverse
    cases answer with
    | Err error => exact Or.inr inverse
    | Ok output =>
      obtain ⟨tail, outputEq, relation⟩ := inverse
      change output.val = [] ++ tail at outputEq
      change List.Forall₂ (EncodesLiteral value) output.val input.val
      exact outputEq.symm ▸ relation

theorem decode_clause_inverse (value : Reservation) (input : alloc.vec.Vec OutputLiteral)
    (output : alloc.vec.Vec InputLiteral) (maximum : Usize)
    (success : Reservation.decode_clause value input maximum = .ok (.Ok output)) :
    List.Forall₂ (EncodesLiteral value) output.val input.val := by
  have checked := decode_clause_inverse_spec value input maximum
  rw [success] at checked
  simpa only [spec_ok, InverseClausePost] using checked

/-- The actual successful decoder supplies every conversion and eligibility
    witness. Only the valid reservation and predicate-preserving model extension
    remain premises; no preexisting equality clause or literal witness is used. -/
theorem decode_clause_success_meaning {D : Type} (original extended : Fang.Interpretation D)
    (value : Reservation) (input : alloc.vec.Vec OutputLiteral) (output : alloc.vec.Vec InputLiteral)
    (maximum : Usize) (functionLimit : Nat) (reservation : ValidReservation value)
    (preserved : Fang.QuantifiedFOF.Skolem.PreservesBelow functionLimit
      (Fang.EqualityBridge.reserveInterpretation value.equality.val original) extended)
    (success : Reservation.decode_clause value input maximum = .ok (.Ok output)) :
    (∀ literal ∈ output.val.map decodeInput,
      Fang.EqualityBridge.AtomEligible value.equality.val literal.atom) ∧
    (Fang.Clause.Valid extended (input.val.map decodeOutput) ↔
      Fang.Equality.clauseValid (Fang.EqualityBridge.recoverInterpretation original extended)
        (output.val.map decodeInput)) := by
  have relation := decode_clause_inverse value input output maximum success
  obtain ⟨eligible, exactClause⟩ := encoded_clause_model value output.val input.val reservation relation
  refine ⟨eligible, ?_⟩
  rw [exactClause]
  exact Fang.EqualityBridge.extended_clause_conversion value.equality.val functionLimit original extended
    (output.val.map decodeInput) eligible preserved

end FangEqualityBridge
