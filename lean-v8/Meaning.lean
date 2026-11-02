/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Representation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityBridge
open fang_fof_equality_bridge

/-- This relates the successful actual Rust clause encoder to mathematical
    equality semantics. Signature completeness and original bytes are separate. -/
theorem encode_clause_meaning {D : Type} (model : Fang.Interpretation D)
    (value : Reservation) (source : alloc.vec.Vec InputLiteral) (target : alloc.vec.Vec OutputLiteral)
    (maximum : Usize) (reservation : ValidReservation value)
    (fits : source.val.length ≤ maximum.val)
    (valid : ∀ literal ∈ source.val, LiteralValid value literal)
    (success : Reservation.encode_clause value source maximum = .ok (.Ok target)) :
    Fang.Clause.Valid (Fang.EqualityBridge.reserveInterpretation value.equality.val model)
      (target.val.map decodeOutput) ↔ Fang.Equality.clauseValid model (source.val.map decodeInput) := by
  have checked := encode_clause_spec value source maximum fits valid
  rw [success] at checked
  simp only [spec_ok] at checked
  obtain ⟨output, same, relation⟩ := checked
  cases same
  obtain ⟨eligible, exactClause⟩ := encoded_clause_model value source.val target.val reservation relation
  rw [exactClause]
  exact Fang.EqualityBridge.clause_encoding_valid value.equality.val model _ eligible

/-- A conversion witness supplies every reserved arity and ordinary head. With
    that witness the actual decoder returns the exact equality clause and its
    meaning in any Skolem extension that preserves all predicates. -/
theorem decode_clause_extended_meaning {D : Type} (original extended : Fang.Interpretation D)
    (value : Reservation) (source : List InputLiteral) (encoded : alloc.vec.Vec OutputLiteral)
    (output : alloc.vec.Vec InputLiteral) (maximum : Usize) (functionLimit : Nat)
    (reservation : ValidReservation value) (fits : encoded.val.length ≤ maximum.val)
    (relation : List.Forall₂ (EncodesLiteral value) source encoded.val)
    (preserved : Fang.QuantifiedFOF.Skolem.PreservesBelow functionLimit
      (Fang.EqualityBridge.reserveInterpretation value.equality.val original) extended)
    (success : Reservation.decode_clause value encoded maximum = .ok (.Ok output)) :
    output.val = source ∧
      (Fang.Clause.Valid extended (encoded.val.map decodeOutput) ↔
        Fang.Equality.clauseValid (Fang.EqualityBridge.recoverInterpretation original extended)
          (output.val.map decodeInput)) := by
  have checked := decode_clause_spec value source encoded maximum reservation fits relation
  rw [success] at checked
  simp only [spec_ok] at checked
  obtain ⟨decoded, same, exactSource⟩ := checked
  cases same
  refine ⟨exactSource, ?_⟩
  obtain ⟨eligible, exactClause⟩ := encoded_clause_model value source encoded.val reservation relation
  rw [exactClause, exactSource]
  exact Fang.EqualityBridge.extended_clause_conversion value.equality.val functionLimit original extended
    (source.map decodeInput) eligible preserved

end FangEqualityBridge
