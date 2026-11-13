/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Checked representation transport from the strict equality byte decoder. -/
import OriginalInput
import EqualityQuantifiedBytes
import ArityTable

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangQuantifiedEqualityInput
open Fang.QuantifiedEqualityFrontend

inductive Error where
  | input : String → Error
  | transport : FangOriginalInput.Error → Error
  | reservation : fang_fof_equality_bridge.Error → Error
  | runtimeEffect
  | divergence

def liftTransport {α : Type} (action : Except FangOriginalInput.Error α) : Except Error α :=
  action.mapError .transport

def observe {α : Type} (action : Result α) : Except Error α :=
  match action.match with
  | .ok value => .ok value
  | .vis _ _ => .error .runtimeEffect
  | .div => .error .divergence

def reserve (table : alloc.vec.Vec Usize) (maximum : Usize) :
    Except Error fang_fof_equality_bridge.Reservation := do
  let result ← observe (fang_fof_equality_bridge.Reservation.new table maximum)
  match result with
  | .Ok value => .ok value
  | .Err error => .error (.reservation error)

/-- The source order is unchanged. Names stay in Prepared.original; the existing
    numeric declaration type stores only the clause or quantified formula. -/
def numericDeclaration : Encoding.EncodedDeclaration → Fang.NamedQuantified.NumericDeclaration
  | .cnf _ clause => .cnf clause
  | .fof _ formula => .fof formula

def numericDeclarations (source : List Encoding.EncodedDeclaration) :
    List Fang.NamedQuantified.NumericDeclaration := source.map numericDeclaration

structure Prepared where
  original : Encoding.Encoded
  declarations : Slice fang_skolem_core.Declaration
  signature : fang_skolem_core.fang_quantified_fof_core.Signature
  reservation : fang_fof_equality_bridge.Reservation

/-- Encode the complete original tables, then run the actual extracted reserve
    and arity-extension functions. The source's claimed equality ID and extended
    table are not used to construct this reservation. Successful source decoding
    proves that they coincide with these results. -/
def transport (source : Encoding.Encoded) (maximum : Usize) : Except Error Prepared := do
  let original ← liftTransport (FangOriginalInput.liftWidth
    (FangQuantifiedTransport.encodeSignature
      (source.functions.map Prod.snd) (source.originalPredicates.map Prod.snd)))
  let reservation ← reserve original.predicates maximum
  let predicates ← observe (fang_fof_equality_bridge.Reservation.extended_arities reservation)
  let declarations ← liftTransport (FangOriginalInput.encodeAxioms
    (Fang.QuantifiedCertificate.formulas (numericDeclarations source.declarations)))
  let declarations ← liftTransport (FangOriginalInput.checkedSlice declarations)
  pure ⟨source, declarations, ⟨original.functions, predicates⟩, reservation⟩

def prepareInput (input : String) (maximum : Usize) : Except Error Prepared := do
  let source ← (Fang.QuantifiedEqualityFrontend.decode input).mapError .input
  transport source maximum

theorem bind_success {α β : Type} {action : Except Error α} {next : α → Except Error β} {output}
    (success : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem mapError_success {α ε : Type} {action : Except ε α} {map : ε → Error} {output}
    (success : action.mapError map = .ok output) : action = .ok output := by
  cases action with
  | error error => cases success
  | ok value => cases Except.ok.inj success; rfl

theorem observe_success {α : Type} {action : Result α} {output}
    (success : observe action = .ok output) : action = .ok output := by
  cases observed : action.match with
  | ok value =>
    have same : value = output := Except.ok.inj (by simpa only [observe, observed] using success)
    subst output
    exact Result.match.isOk.mp observed
  | vis effect next => simp [observe, observed] at success
  | div => simp [observe, observed] at success

theorem reserve_success {table maximum value} (success : reserve table maximum = .ok value) :
    fang_fof_equality_bridge.Reservation.new table maximum = .ok (.Ok value) := by
  obtain ⟨answer, observed, accepted⟩ := bind_success success
  cases answer with
  | Err error => cases accepted
  | Ok result => cases Except.ok.inj accepted; exact observe_success observed

theorem transport_runs {source maximum prepared} (success : transport source maximum = .ok prepared) :
    prepared.original = source ∧ ∃ original declarations,
      FangQuantifiedTransport.encodeSignature
        (source.functions.map Prod.snd) (source.originalPredicates.map Prod.snd) = .ok original ∧
      fang_fof_equality_bridge.Reservation.new original.predicates maximum = .ok (.Ok prepared.reservation) ∧
      fang_fof_equality_bridge.Reservation.extended_arities prepared.reservation = .ok prepared.signature.predicates ∧
      prepared.signature.functions = original.functions ∧
      FangOriginalInput.encodeAxioms
        (Fang.QuantifiedCertificate.formulas (numericDeclarations source.declarations)) = .ok declarations ∧
      prepared.declarations.val = declarations := by
  obtain ⟨original, signatureRun, success⟩ := bind_success success
  obtain ⟨reservation, reservationRun, success⟩ := bind_success success
  obtain ⟨predicates, extensionRun, success⟩ := bind_success success
  obtain ⟨declarations, declarationsRun, success⟩ := bind_success success
  obtain ⟨slice, sliceRun, success⟩ := bind_success success
  cases Except.ok.inj success
  exact ⟨rfl, original, declarations,
    FangOriginalInput.liftWidth_success (mapError_success signatureRun),
    reserve_success reservationRun, observe_success extensionRun, rfl,
    mapError_success declarationsRun, FangOriginalInput.checkedSlice_values (mapError_success sliceRun)⟩

theorem prepareInput_runs {input maximum prepared}
    (success : prepareInput input maximum = .ok prepared) :
    Fang.QuantifiedEqualityFrontend.decode input = .ok prepared.original ∧
      transport prepared.original maximum = .ok prepared := by
  obtain ⟨source, decoded, transported⟩ := bind_success success
  have same := (transport_runs transported).1
  rw [same]
  exact ⟨mapError_success decoded, transported⟩

/-- Complete supplied arity tables, actual reservation validity and room for the
    extra binary slot follow from the successful transport itself. -/
theorem transport_tables {source maximum prepared}
    (success : transport source maximum = .ok prepared) :
    FangEqualityBridge.ValidReservation prepared.reservation ∧
    prepared.reservation.original_predicates.val.map (fun value => value.val) =
      source.originalPredicates.map Prod.snd ∧
    prepared.reservation.equality.val = source.originalPredicates.length ∧
    prepared.reservation.equality.val < maximum.val ∧
    prepared.signature.functions.val.map (fun value => value.val) = source.functions.map Prod.snd ∧
    prepared.signature.predicates.val.map (fun value => value.val) =
      source.originalPredicates.map Prod.snd ++ [2] := by
  obtain ⟨_, original, declarations, signatureRun, reservationRun, extensionRun, functionsEq, _, _⟩ :=
    transport_runs success
  have tables := FangQuantifiedTransport.encodeSignature_values signatureRun
  have reserved := FangEqualityBridge.reservation_new_spec original.predicates maximum
  rw [reservationRun] at reserved
  simp only [spec_ok] at reserved
  obtain ⟨originalEq, valid, room⟩ := reserved
  have tableEq : prepared.reservation.original_predicates.val.map (fun value => value.val) =
      source.originalPredicates.map Prod.snd := by rw [originalEq]; exact tables.2
  have count : prepared.reservation.original_predicates.val.length = source.originalPredicates.length := by
    simpa only [List.length_map] using congrArg List.length tableEq
  have extended := FangEqualityBridge.extended_arities_spec prepared.reservation (by
    rw [originalEq]
    exact Nat.lt_of_lt_of_le room (by scalar_tac))
  rw [extensionRun] at extended
  simp only [spec_ok] at extended
  refine ⟨valid, tableEq, valid.trans count, ?_, ?_, ?_⟩
  · rw [valid, originalEq]
    exact room
  · rw [functionsEq]
    exact tables.1
  · rw [extended, List.map_append, tableEq]
    rfl

/-- The reserved ID and complete extended table now refer to the actual original
    byte decoder, not a caller-supplied reservation/table assumption. -/
theorem prepareInput_tables {input maximum prepared}
    (success : prepareInput input maximum = .ok prepared) :
    FangEqualityBridge.ValidReservation prepared.reservation ∧
    prepared.reservation.equality.val = prepared.original.equalityId ∧
    prepared.reservation.original_predicates.val.map (fun value => value.val) =
      prepared.original.originalPredicates.map Prod.snd ∧
    prepared.signature.functions.val.map (fun value => value.val) =
      prepared.original.functions.map Prod.snd ∧
    prepared.signature.predicates.val.map (fun value => value.val) = prepared.original.predicateArities := by
  obtain ⟨decoded, transported⟩ := prepareInput_runs success
  obtain ⟨_, _, _, encoded⟩ := Fang.QuantifiedEqualityFrontend.decode_byte_encoding decoded
  have slot := Encoding.encode_reserved_slot encoded
  obtain ⟨valid, original, count, _, functions, predicates⟩ := transport_tables transported
  exact ⟨valid, count.trans slot.1.symm, original, functions, predicates.trans slot.2.symm⟩

end FangQuantifiedEqualityInput
