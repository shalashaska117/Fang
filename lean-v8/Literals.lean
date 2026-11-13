/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact literal conversion over the generated Rust definitions. -/
import Reservation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityBridge
open fang_fof_equality_bridge

def OrdinaryAnswer (value : Reservation) (predicate : U32) (arity : Usize) :
    core.result.Result Unit fang_fof_equality_bridge.Error :=
  if h : predicate.val < value.original_predicates.val.length then
    if value.original_predicates.val[predicate.val] = arity then .Ok ()
    else .Err .PredicateArity
  else .Err .UnknownPredicate

/-- The predicate-table check terminates and returns the exact head/arity error. -/
theorem ordinary_spec (value : Reservation) (predicate : U32) (arity : Usize) :
    Reservation.ordinary value predicate arity ⦃ fun answer =>
      answer = OrdinaryAnswer value predicate arity ⦄ := by
  have cast_eq : (UScalar.cast .Usize predicate).val = predicate.val := U32.cast_Usize_val_eq _
  unfold Reservation.ordinary
  simp only [lift, bind_ok]
  split
  next outside =>
    have invalid : ¬ predicate.val < value.original_predicates.val.length := by scalar_tac
    simp [OrdinaryAnswer, invalid]
  next inside =>
    have valid : predicate.val < value.original_predicates.val.length := by scalar_tac
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec value.original_predicates
      (UScalar.cast .Usize predicate) (by scalar_tac))
    intro arityFound found
    subst arityFound
    simp only [cast_eq]
    by_cases same : value.original_predicates.val[predicate.val] = arity
    · simp [same, OrdinaryAnswer, valid]
    · simp [same, OrdinaryAnswer, valid]

theorem encode_predicate_spec (value : Reservation) (positive : Bool) (predicate : U32)
    (arguments : alloc.vec.Vec fang.syntax.Term)
    (valid : OrdinaryAnswer value predicate (alloc.vec.Vec.len arguments) = .Ok ()) :
    Reservation.encode_literal value ⟨positive, .Predicate predicate arguments⟩
      ⦃ fun answer => answer = .Ok ⟨positive, predicate, arguments⟩ ⦄ := by
  unfold Reservation.encode_literal
  apply spec_bind (ordinary_spec value predicate (alloc.vec.Vec.len arguments))
  intro answer checked
  rw [valid] at checked
  subst answer
  simp [core.result.Result.Insts.CoreOpsTry.branch]

/-- Both operands are moved in order, with no recursive transformation. -/
theorem encode_equality_spec (value : Reservation) (positive : Bool)
    (left right : fang.syntax.Term) :
    Reservation.encode_literal value ⟨positive, .Equal left right⟩
      ⦃ fun answer => ∃ arguments,
        answer = .Ok ⟨positive, value.equality, arguments⟩ ∧
        arguments.val = [left, right] ⦄ := by
  unfold Reservation.encode_literal
  apply spec_bind (alloc.vec.Vec.push_spec
    (alloc.vec.Vec.with_capacity fang.syntax.Term 2#usize) left (by
      change 0 < Usize.max
      scalar_tac))
  intro first first_eq
  change first.val = [] ++ [left] at first_eq
  apply spec_bind (alloc.vec.Vec.push_spec first right (by
    have length_eq := congrArg List.length first_eq
    simp only [List.length_append, List.length_nil, List.length_cons] at length_eq
    scalar_tac))
  intro second second_eq
  simp only [spec_ok]
  refine ⟨second, rfl, ?_⟩
  rw [second_eq, first_eq]
  rfl

end FangEqualityBridge
