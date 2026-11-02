/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Literals

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityBridge
open fang_fof_equality_bridge

attribute [local implicit_reducible] alloc.vec.into_iter.IntoIter

theorem iterator_next_cons {T : Type} (iter : alloc.vec.into_iter.IntoIter T)
    (head : T) (tail : List T) (shape : iter.val = head :: tail) :
    ∃ bound, alloc.vec.into_iter.IteratorIntoIter.next iter =
      ok (some head, alloc.vec.Vec.from tail bound) := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next
  split
  · rename_i empty
    simp [shape] at empty
  · rename_i head' tail' nonempty
    have equal : head' = head ∧ tail' = tail := by simpa [shape] using nonempty.symm
    obtain ⟨rfl, rfl⟩ := equal
    have bound : tail'.length ≤ Usize.max := by
      have original := iter.property
      rw [shape] at original
      simp only [List.length_cons] at original
      omega
    exact ⟨bound, rfl⟩

theorem decode_equality_spec (value : Reservation) (positive : Bool)
    (arguments : alloc.vec.Vec fang.syntax.Term) (left right : fang.syntax.Term)
    (shape : arguments.val = [left, right]) :
    Reservation.decode_literal value ⟨positive, value.equality, arguments⟩
      ⦃ fun answer => answer = .Ok ⟨positive, .Equal left right⟩ ⦄ := by
  have length_eq : alloc.vec.Vec.len arguments = 2#usize := by
    apply UScalar.eq_of_val_eq
    simp [alloc.vec.Vec.len, shape]
  obtain ⟨tailBound, first⟩ := iterator_next_cons arguments left [right] shape
  obtain ⟨emptyBound, second⟩ := iterator_next_cons
    (alloc.vec.Vec.from [right] tailBound) right [] rfl
  simp [Reservation.decode_literal, length_eq,
    alloc.vec.IntoIteratorVec.into_iter, first,
    Aeneas.Std.uncurry, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
    second]

/-- A checked original predicate cannot be confused with the reserved head. -/
theorem decode_predicate_spec (value : Reservation) (positive : Bool) (predicate : U32)
    (arguments : alloc.vec.Vec fang.syntax.Term) (reservation : ValidReservation value)
    (valid : OrdinaryAnswer value predicate (alloc.vec.Vec.len arguments) = .Ok ()) :
    Reservation.decode_literal value ⟨positive, predicate, arguments⟩
      ⦃ fun answer => answer = .Ok ⟨positive, .Predicate predicate arguments⟩ ⦄ := by
  have below : predicate.val < value.original_predicates.val.length := by
    unfold OrdinaryAnswer at valid
    split at valid
    · assumption
    · contradiction
  have distinct : predicate ≠ value.equality := by
    intro same
    rw [same, reservation] at below
    omega
  simp only [Reservation.decode_literal, distinct, ↓reduceIte]
  apply spec_bind (ordinary_spec value predicate (alloc.vec.Vec.len arguments))
  intro answer checked
  rw [valid] at checked
  subst answer
  simp [core.result.Result.Insts.CoreOpsTry.branch]

/-- An actual encode/decode composition returns the whole original literal.
    The table/ordinary-arity premise excludes a user atom at the reserved ID. -/
theorem literal_roundtrip (value : Reservation)
    (literal : fang_equality_inference_core.Literal) (reservation : ValidReservation value)
    (valid : match literal.atom with
      | .Predicate predicate arguments =>
          OrdinaryAnswer value predicate (alloc.vec.Vec.len arguments) = .Ok ()
      | .Equal _ _ => True) :
    (do
      let encoded ← Reservation.encode_literal value literal
      match encoded with
      | .Err error => ok (core.result.Result.Err error)
      | .Ok encoded => Reservation.decode_literal value encoded)
      ⦃ fun answer => answer = .Ok literal ⦄ := by
  cases literal with
  | mk positive atom =>
    cases atom with
    | Predicate predicate arguments =>
      apply spec_bind (encode_predicate_spec value positive predicate arguments valid)
      intro answer encoded
      subst answer
      exact decode_predicate_spec value positive predicate arguments reservation valid
    | Equal left right =>
      apply spec_bind (encode_equality_spec value positive left right)
      intro answer encoded
      obtain ⟨arguments, rfl, shape⟩ := encoded
      exact decode_equality_spec value positive arguments left right shape

end FangEqualityBridge
