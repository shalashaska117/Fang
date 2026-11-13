/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Contracts over the actual generated reserved-ID functions. -/
import FofEqualityBridge

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityBridge
open fang_fof_equality_bridge

def ReservedPost (count maximum : Usize)
    (answer : core.result.Result U32 fang_fof_equality_bridge.Error) : Prop :=
  if maximum.val ≤ count.val then answer = .Err .PredicateLimit
  else if 4294967295 < count.val then answer = .Err .SymbolId
  else ∃ id, answer = .Ok id ∧ id.val = count.val

/-- The capacity error has precedence over scalar overflow. Success reserves the
    first ID outside the original table. This says nothing about source bytes. -/
theorem reserved_id_spec (count maximum : Usize) :
    reserved_id count maximum ⦃ ReservedPost count maximum ⦄ := by
  have cast_max : (UScalar.cast .Usize core.num.U32.MAX).val = 4294967295 := by
    rw [U32.cast_Usize_val_eq]
    rfl
  unfold reserved_id
  split
  next full =>
    have h : maximum.val ≤ count.val := by scalar_tac
    simp [ReservedPost, h]
  next available =>
    have h : ¬ maximum.val ≤ count.val := by scalar_tac
    simp only [lift, bind_ok]
    split
    next tooLarge =>
      have large : 4294967295 < count.val := by scalar_tac
      simp [ReservedPost, h, large]
    next fits =>
      have small : ¬ 4294967295 < count.val := by scalar_tac
      simp only [spec_ok, ReservedPost, h, small, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      rw [UScalar.cast_val_eq]
      apply Nat.mod_eq_of_lt
      scalar_tac

def ValidReservation (value : Reservation) : Prop :=
  value.equality.val = value.original_predicates.val.length

/-- Construction retains the complete supplied table and checks the additional
    slot. Completeness of that supplied table remains a caller obligation. -/
theorem reservation_new_spec (table : alloc.vec.Vec Usize) (maximum : Usize) :
    Reservation.new table maximum ⦃ fun answer =>
      match answer with
      | .Ok value => value.original_predicates = table ∧ ValidReservation value ∧
          table.val.length < maximum.val
      | .Err .PredicateLimit => maximum.val ≤ table.val.length
      | .Err .SymbolId => table.val.length < maximum.val ∧ 4294967295 < table.val.length
      | .Err _ => False ⦄ := by
  unfold Reservation.new
  apply spec_bind (reserved_id_spec (alloc.vec.Vec.len table) maximum)
  intro answer post
  unfold ReservedPost at post
  split at post
  next full =>
    subst answer
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using full
  next available =>
    split at post
    next large =>
      subst answer
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      constructor <;> scalar_tac
    next fits =>
      obtain ⟨id, rfl, exactId⟩ := post
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, spec_ok, ValidReservation]
      exact ⟨trivial, exactId, by scalar_tac⟩

theorem equality_id_spec (value : Reservation) :
    Reservation.equality_id value ⦃ fun id => id = value.equality ⦄ := by
  simp [Reservation.equality_id]

end FangEqualityBridge
