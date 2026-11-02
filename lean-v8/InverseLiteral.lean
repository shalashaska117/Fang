/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ClauseEncoding

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityBridge
open fang_fof_equality_bridge

def DecodeError (error : fang_fof_equality_bridge.Error) : Prop :=
  error = .ReservedArity ∨ error = .UnknownPredicate ∨ error = .PredicateArity

def DecodeLiteralPost (value : Reservation) (target : OutputLiteral)
    (answer : core.result.Result InputLiteral fang_fof_equality_bridge.Error) : Prop :=
  match answer with
  | .Ok source => EncodesLiteral value source target
  | .Err error => DecodeError error

theorem two_entries {T : Type} (items : List T) (length : items.length = 2) :
    ∃ left right, items = [left, right] := by
  cases items with
  | nil => simp at length
  | cons left rest =>
    cases rest with
    | nil => simp at length
    | cons right tail =>
      have empty : tail = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using length
      exact ⟨left, right, by rw [empty]⟩

/-- Every successful actual literal decoding supplies its conversion witness.
    No preexisting equality literal or valid-head premise is needed. -/
theorem decode_literal_inverse_spec (value : Reservation) (target : OutputLiteral) :
    Reservation.decode_literal value target ⦃ DecodeLiteralPost value target ⦄ := by
  cases target with
  | mk positive predicate arguments =>
    by_cases reserved : predicate = value.equality
    · subst predicate
      by_cases pair : arguments.val.length = 2
      · obtain ⟨left, right, shape⟩ := two_entries arguments.val pair
        apply spec_mono (decode_equality_spec value positive arguments left right shape)
        intro answer decoded
        subst answer
        exact ⟨rfl, rfl, shape⟩
      · have wrong : alloc.vec.Vec.len arguments != 2#usize := by scalar_tac
        simp [Reservation.decode_literal, wrong, DecodeLiteralPost, DecodeError]
    · simp only [Reservation.decode_literal, reserved, ↓reduceIte]
      apply spec_bind (ordinary_spec value predicate (alloc.vec.Vec.len arguments))
      intro answer checked
      cases answer with
      | Ok checkedUnit =>
        cases checkedUnit
        have valid : LiteralValid value ⟨positive, .Predicate predicate arguments⟩ := checked.symm
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, spec_ok, DecodeLiteralPost]
        exact ⟨rfl, valid, rfl, rfl⟩
      | Err error =>
        have failure : DecodeError error := by
          unfold OrdinaryAnswer at checked
          split at checked
          · split at checked <;> simp_all [DecodeError]
          · simp_all [DecodeError]
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          DecodeLiteralPost] using failure

theorem decode_literal_inverse (value : Reservation) (target : OutputLiteral) (source : InputLiteral)
    (success : Reservation.decode_literal value target = .ok (.Ok source)) :
    EncodesLiteral value source target := by
  have checked := decode_literal_inverse_spec value target
  rw [success] at checked
  simpa only [spec_ok, DecodeLiteralPost] using checked

end FangEqualityBridge
