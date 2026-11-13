/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ClauseEncoding

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityBridge
open fang_fof_equality_bridge

attribute [local implicit_reducible] alloc.vec.into_iter.IntoIter
attribute [local implicit_reducible] alloc.vec.Vec.val Slice.val

theorem encoded_lengths {value : Reservation} {source : List InputLiteral} {target : List OutputLiteral}
    (encoded : List.Forall₂ (EncodesLiteral value) source target) : source.length = target.length := by
  induction encoded with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem decode_clause_loop_spec (iter : alloc.vec.into_iter.IntoIter OutputLiteral)
    (value : Reservation) (result : alloc.vec.Vec InputLiteral) (source : List InputLiteral)
    (reservation : ValidReservation value)
    (capacity : result.val.length + iter.val.length ≤ Usize.max)
    (encoded : List.Forall₂ (EncodesLiteral value) source iter.val) :
    Reservation.decode_clause_loop iter value result ⦃ fun answer => ∃ output,
      answer = .Ok output ∧ output.val = result.val ++ source ⦄ := by
  with_unfolding_all
    cases iter with
    | mk slice =>
      rw [Reservation.decode_clause_loop.eq_def]
      change List.Forall₂ (EncodesLiteral value) source slice.val at encoded
      cases remaining : slice.val with
      | nil =>
        rw [remaining] at encoded
        have empty : source = [] := by cases encoded; rfl
        rw [iterator_next_nil _ remaining]
        simp [Aeneas.Std.uncurry, empty]
      | cons literal rest =>
        rw [remaining] at encoded
        obtain ⟨head, tail, sourceEq, relation, remainder⟩ : ∃ head tail,
            source = head :: tail ∧ EncodesLiteral value head literal ∧
              List.Forall₂ (EncodesLiteral value) tail rest := by
          cases encoded with
          | cons relation remainder => exact ⟨_, _, rfl, relation, remainder⟩
        obtain ⟨restBound, nextEq⟩ := iterator_next_cons _ literal rest remaining
        rw [nextEq]
        simp only [bind_ok, Aeneas.Std.uncurry]
        apply spec_bind (decode_encoded_spec value head literal reservation relation)
        intro answer decoded
        subst answer
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        apply spec_bind (alloc.vec.Vec.push_spec result head (by
          change result.val.length + slice.val.length ≤ Usize.max at capacity
          rw [remaining] at capacity
          simp only [List.length_cons] at capacity
          omega))
        intro extended extendedEq
        apply spec_mono (decode_clause_loop_spec _ value extended tail reservation (by
          simp only [alloc.vec.Vec.from_val]
          rw [extendedEq, List.length_append]
          change result.val.length + slice.val.length ≤ Usize.max at capacity
          rw [remaining] at capacity
          simp only [List.length_cons, List.length_nil] at capacity ⊢
          omega) (by simpa only [alloc.vec.Vec.from_val] using remainder))
        intro answer decodedRest
        obtain ⟨output, rfl, outputEq⟩ := decodedRest
        refine ⟨output, rfl, ?_⟩
        rw [outputEq, extendedEq, sourceEq, List.append_assoc]
        rfl
termination_by iter.val.length
decreasing_by
  subst iter
  change (alloc.vec.Vec.from rest restBound).val.length < slice.val.length
  rw [alloc.vec.Vec.from_val, remaining]
  simp

theorem decode_clause_spec (value : Reservation) (source : List InputLiteral)
    (clause : alloc.vec.Vec OutputLiteral) (maximum : Usize)
    (reservation : ValidReservation value) (fits : clause.val.length ≤ maximum.val)
    (encoded : List.Forall₂ (EncodesLiteral value) source clause.val) :
    Reservation.decode_clause value clause maximum ⦃ fun answer => ∃ output,
      answer = .Ok output ∧ output.val = source ⦄ := by
  have within : ¬ alloc.vec.Vec.len clause > maximum := by scalar_tac
  simp only [Reservation.decode_clause, within, ↓reduceIte,
    alloc.vec.IntoIteratorVec.into_iter, bind_ok]
  apply spec_mono (decode_clause_loop_spec clause value (alloc.vec.Vec.new InputLiteral)
    source reservation (by simp) encoded)
  intro answer decoded
  obtain ⟨output, rfl, exactSource⟩ := decoded
  exact ⟨output, rfl, exactSource⟩

/-- The actual ordered clause composition returns every original literal and
    duplicate. Native allocator failures are not part of this extracted model. -/
theorem clause_roundtrip (value : Reservation) (clause : alloc.vec.Vec InputLiteral)
    (maximum : Usize) (reservation : ValidReservation value)
    (fits : clause.val.length ≤ maximum.val)
    (valid : ∀ literal ∈ clause.val, LiteralValid value literal) :
    (do
      let encoded ← Reservation.encode_clause value clause maximum
      match encoded with
      | .Err error => ok (core.result.Result.Err error)
      | .Ok encoded => Reservation.decode_clause value encoded maximum)
      ⦃ fun answer => answer = .Ok clause ⦄ := by
  apply spec_bind (encode_clause_spec value clause maximum fits valid)
  intro answer encoded
  obtain ⟨encoded, rfl, relation⟩ := encoded
  apply spec_mono (decode_clause_spec value clause.val encoded maximum reservation
    (by rw [← encoded_lengths relation]; exact fits) relation)
  intro answer decoded
  obtain ⟨output, rfl, same⟩ := decoded
  have exactOutput : output = clause := by
    apply alloc.vec.Vec.ext
    exact same
  rw [exactOutput]

theorem encode_clause_limit (value : Reservation) (clause : alloc.vec.Vec InputLiteral)
    (maximum : Usize) (exceeded : maximum.val < clause.val.length) :
    Reservation.encode_clause value clause maximum = .ok (.Err .LiteralLimit) := by
  have outside : alloc.vec.Vec.len clause > maximum := by scalar_tac
  simp [Reservation.encode_clause, outside]

theorem decode_clause_limit (value : Reservation) (clause : alloc.vec.Vec OutputLiteral)
    (maximum : Usize) (exceeded : maximum.val < clause.val.length) :
    Reservation.decode_clause value clause maximum = .ok (.Err .LiteralLimit) := by
  have outside : alloc.vec.Vec.len clause > maximum := by scalar_tac
  simp [Reservation.decode_clause, outside]

end FangEqualityBridge
