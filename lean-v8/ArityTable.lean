/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Reservation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityBridge
open fang_fof_equality_bridge

theorem extended_arities_loop_spec (value : Reservation) (copied : alloc.vec.Vec Usize)
    (index : Usize) (copiedPrefix : copied.val = value.original_predicates.val.take index.val) :
    Reservation.extended_arities_loop value copied index
      ⦃ fun output => output = value.original_predicates ⦄ := by
  unfold Reservation.extended_arities_loop
  dsimp only
  split
  next inside =>
    have indexBound : index.val < value.original_predicates.val.length := by scalar_tac
    have copiedLength : copied.val.length = index.val := by
      rw [copiedPrefix, List.length_take]
      omega
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec value.original_predicates index indexBound)
    intro arity found
    subst arity
    apply spec_bind (alloc.vec.Vec.push_spec copied value.original_predicates.val[index.val] (by
      have bound := value.original_predicates.property
      omega))
    intro extended copiedEq
    apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    intro next nextEq
    have nextVal : next.val = index.val + 1 := by simpa using nextEq
    apply extended_arities_loop_spec value extended next
    rw [copiedEq, copiedPrefix, nextVal]
    exact (List.take_succ_eq_append_getElem indexBound).symm
  next outside =>
    have finished : value.original_predicates.val.length ≤ index.val := by scalar_tac
    have exactCopy : copied = value.original_predicates := by
      apply alloc.vec.Vec.ext
      rw [copiedPrefix, List.take_of_length_le finished]
    simp [exactCopy]
termination_by value.original_predicates.val.length - index.val
decreasing_by scalar_tac

/-- The actual table builder preserves every original arity and appends exactly
    the binary equality entry. The successful constructor provides this room. -/
theorem extended_arities_spec (value : Reservation)
    (room : value.original_predicates.val.length < Usize.max) :
    Reservation.extended_arities value ⦃ fun output =>
      output.val = value.original_predicates.val ++ [2#usize] ⦄ := by
  unfold Reservation.extended_arities
  apply spec_bind (extended_arities_loop_spec value (alloc.vec.Vec.new Usize) 0#usize (by simp))
  intro copied exactCopy
  subst copied
  exact alloc.vec.Vec.push_spec value.original_predicates 2#usize room

end FangEqualityBridge
