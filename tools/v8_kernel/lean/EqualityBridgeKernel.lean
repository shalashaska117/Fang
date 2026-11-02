/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft exact-call adapters over the unchanged equality bridge specifications. -/
import EqualityClauseReplay
import ArityTable

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangEqualityKernelGenerator

theorem eq_of_exact_spec {α : Type} {action : Result α} {value : α}
    (specification : action ⦃ fun result => result = value ⦄) : action = .ok value := by
  cases observed : action.match with
  | ok result =>
    have same := Result.match.isOk.mp observed
    rw [same] at specification
    have valueEq := (WP.spec_ok _).mp specification
    exact same.trans (congrArg Result.ok valueEq)
  | vis effect next =>
    rw [Result.match.isVis.mp observed] at specification
    exact False.elim ((WP.spec_vis _ _).mp specification)
  | div =>
    rw [Result.match.isDiv.mp observed] at specification
    exact False.elim (WP.spec_div.mp specification)

theorem reserved_id_eq (count maximum : Usize) (identifier : U32)
    (room : count.val < maximum.val) (index : identifier.val = count.val) :
    fang_fof_equality_bridge.reserved_id count maximum = .ok (.Ok identifier) := by
  apply eq_of_exact_spec
  apply spec_mono (FangEqualityBridge.reserved_id_spec count maximum)
  intro answer post
  have fits : ¬ 4294967295 < count.val := by scalar_tac
  have available : ¬ maximum.val ≤ count.val := by omega
  simp only [FangEqualityBridge.ReservedPost, available, fits, ↓reduceIte] at post
  obtain ⟨actual, rfl, same⟩ := post
  congr 1
  apply UScalar.eq_of_val_eq
  exact same.trans index.symm

theorem reservation_eq (table : alloc.vec.Vec Usize) (maximum : Usize) (identifier : U32)
    (room : table.val.length < maximum.val) (index : identifier.val = table.val.length) :
    fang_fof_equality_bridge.Reservation.new table maximum =
      .ok (.Ok ⟨table, identifier⟩) := by
  have reserved := reserved_id_eq (alloc.vec.Vec.len table) maximum identifier
    (by simpa using room) (by simpa using index)
  simp only [fang_fof_equality_bridge.Reservation.new, reserved, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch]

theorem extended_arities_eq (reservation : fang_fof_equality_bridge.Reservation)
    (target : alloc.vec.Vec Usize)
    (room : reservation.original_predicates.val.length < Usize.max)
    (values : target.val = reservation.original_predicates.val ++ [2#usize]) :
    fang_fof_equality_bridge.Reservation.extended_arities reservation = .ok target := by
  apply eq_of_exact_spec
  apply spec_mono (FangEqualityBridge.extended_arities_spec reservation room)
  intro actual actualValues
  apply alloc.vec.Vec.ext
  exact actualValues.trans values.symm

theorem decode_clause_eq (reservation : fang_fof_equality_bridge.Reservation)
    (source : alloc.vec.Vec FangEqualityBridge.OutputLiteral)
    (target : alloc.vec.Vec FangEqualityBridge.InputLiteral) (maximum : Usize)
    (valid : FangEqualityBridge.ValidReservation reservation)
    (fits : source.val.length ≤ maximum.val)
    (encoded : List.Forall₂ (FangEqualityBridge.EncodesLiteral reservation) target.val source.val) :
    fang_fof_equality_bridge.Reservation.decode_clause reservation source maximum = .ok (.Ok target) := by
  apply eq_of_exact_spec
  apply spec_mono (FangEqualityBridge.decode_clause_spec reservation target.val source maximum
    valid fits encoded)
  intro answer post
  obtain ⟨actual, rfl, values⟩ := post
  congr 1
  apply alloc.vec.Vec.ext
  exact values

theorem conversion_clause_eq (reservation : fang_fof_equality_bridge.Reservation)
    (maximum : Usize) (source : Fang.Clause)
    (encoded : alloc.vec.Vec FangEqualityBridge.OutputLiteral)
    (converted : alloc.vec.Vec FangEqualityBridge.InputLiteral)
    (encodeRun : FangQuantifiedEqualityReplay.Transport.encodeClause source = .ok encoded)
    (decodeRun : fang_fof_equality_bridge.Reservation.decode_clause reservation encoded maximum =
      .ok (.Ok converted)) :
    FangQuantifiedEqualityReplay.Conversion.clause reservation maximum source =
      .ok (converted.val.map FangEqualityBridge.decodeInput) := by
  simp [FangQuantifiedEqualityReplay.Conversion.clause, encodeRun, decodeRun,
    FangQuantifiedEqualityInput.observe, Except.mapError, Bind.bind, Except.bind]

#print axioms FangEqualityKernelGenerator.eq_of_exact_spec
#print axioms FangEqualityKernelGenerator.reserved_id_eq
#print axioms FangEqualityKernelGenerator.reservation_eq
#print axioms FangEqualityKernelGenerator.extended_arities_eq
#print axioms FangEqualityKernelGenerator.decode_clause_eq
#print axioms FangEqualityKernelGenerator.conversion_clause_eq
end FangEqualityKernelGenerator
