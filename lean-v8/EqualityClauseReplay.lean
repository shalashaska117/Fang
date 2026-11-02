/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EqualityClauseTransport

open Aeneas Aeneas.Std

namespace FangQuantifiedEqualityReplay

theorem bind_success {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output}
    (success : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem mapError_success {α ε δ : Type} {action : Except ε α} {map : ε → δ} {output}
    (success : action.mapError map = .ok output) : action = .ok output := by
  cases action with
  | error error => cases success
  | ok value => cases Except.ok.inj success; rfl

namespace Conversion

inductive Error where
  | encoding : FangQuantifiedTransport.Error → Error
  | observation : FangQuantifiedEqualityInput.Error → Error
  | conversion : fang_fof_equality_bridge.Error → Error

/-- Structural encoding is checked for scalar/vector width. Equality conversion
    remains the actual extracted Rust call, with its own literal/head checks. -/
def clause (reservation : fang_fof_equality_bridge.Reservation) (maximum : Usize)
    (source : Fang.Clause) : Except Error Fang.Equality.Clause := do
  let encoded ← (Transport.encodeClause source).mapError .encoding
  let result ← (FangQuantifiedEqualityInput.observe
    (fang_fof_equality_bridge.Reservation.decode_clause reservation encoded maximum)).mapError .observation
  match result with
  | .Err error => .error (.conversion error)
  | .Ok output => .ok (output.val.map FangEqualityBridge.decodeInput)

/-- Every mixed clause is converted in order, including empty and repeated
    clauses. No output is returned if any conversion fails. -/
def problem (reservation : fang_fof_equality_bridge.Reservation) (maximum : Usize) :
    Fang.Problem → Except Error Fang.Equality.Problem
  | [] => .ok []
  | source :: rest => do pure ((← clause reservation maximum source) :: (← problem reservation maximum rest))

theorem clause_actual {reservation maximum source target}
    (success : clause reservation maximum source = .ok target) :
    FangQuantifiedEquality.ActualClauseConversion reservation source target := by
  obtain ⟨encoded, encodedRun, success⟩ := bind_success success
  obtain ⟨answer, observed, success⟩ := bind_success success
  cases answer with
  | Err error => cases success
  | Ok output =>
    cases Except.ok.inj success
    exact ⟨encoded, output, maximum,
      FangQuantifiedEqualityInput.observe_success (mapError_success observed),
      (Transport.encodeClause_decode (mapError_success encodedRun)).symm, rfl⟩

theorem problem_actual {reservation maximum source target}
    (success : problem reservation maximum source = .ok target) :
    FangQuantifiedEquality.ActualProblemConversion reservation source target := by
  induction source generalizing target with
  | nil => cases Except.ok.inj success; exact .nil
  | cons clause rest ih =>
    obtain ⟨head, converted, success⟩ := bind_success success
    obtain ⟨tail, convertedTail, success⟩ := bind_success success
    cases Except.ok.inj success
    exact .cons (clause_actual converted) (ih convertedTail)

theorem problem_counts {reservation maximum source target}
    (success : problem reservation maximum source = .ok target) :
    source.length = target.length ∧ source.map List.length = target.map List.length :=
  ⟨FangQuantifiedEquality.actualProblem_clause_count (problem_actual success),
   FangQuantifiedEquality.actualProblem_literal_counts (problem_actual success)⟩

end Conversion
end FangQuantifiedEqualityReplay
