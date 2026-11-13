/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Reuse the accepted checked widths and actual Reservation calls. -/
import ExpandedBounds
import ReservedModels
import ProblemComposition

namespace Fang.TptpCandidate.FullFof.Integration
open Aeneas.Std
open Fang.QuantifiedEqualityFrontend Fang.QuantifiedCertificate FangQuantifiedPipeline

def taggedName : Name → String
  | .atom sourceName => "atom:" ++ sourceName
  | .integer sourceName => "integer:" ++ sourceName

def legacyDeclaration (sourceName : Name) : NumericDeclaration → Encoding.EncodedDeclaration
  | .cnf clause => .cnf (taggedName sourceName) clause
  | .fof formula => .fof (taggedName sourceName) formula

/-- This is a representation adapter for the existing checked transport. The
    complete original rows remain in NumericInput, including zero-output rows. -/
def legacyRows (rows : List NumericRow) : List Encoding.EncodedDeclaration :=
  rows.flatMap (fun row => row.declarations.map (legacyDeclaration row.original.name))

def legacyInput (input : NumericInput) : Encoding.Encoded where
  functions := input.functions
  originalPredicates := input.predicates
  equalityId := input.predicates.length
  predicateArities := input.predicates.map Prod.snd ++ [2]
  declarations := legacyRows input.rows

theorem legacy_declaration_numeric (sourceName : Name) (value : NumericDeclaration) :
    FangQuantifiedEqualityInput.numericDeclaration (legacyDeclaration sourceName value) = value := by
  cases value <;> rfl

theorem map_identity {α : Type} : ∀ values : List α, values.map (fun value => value) = values
  | [] => rfl
  | head :: tail => congrArg (List.cons head) (map_identity tail)

theorem legacy_rows_numeric (rows : List NumericRow) :
    FangQuantifiedEqualityInput.numericDeclarations (legacyRows rows) =
      rows.flatMap NumericRow.declarations := by
  simp only [FangQuantifiedEqualityInput.numericDeclarations, legacyRows, List.map_flatMap,
    List.map_map, Function.comp_def, legacy_declaration_numeric]
  exact congrArg (fun select => rows.flatMap select) (funext fun row => map_identity row.declarations)

theorem legacy_models {D : Type} {input : NumericInput} {model : Interpretation D}
    (holds : NamedQuantified.NumericModels model input.declarations) :
    Encoding.Models model (legacyInput input).declarations := by
  intro declaration member
  obtain ⟨row, rowMember, mappedMember⟩ := List.mem_flatMap.mp member
  obtain ⟨item, itemMember, rfl⟩ := List.mem_map.mp mappedMember
  have valid := holds item (List.mem_flatMap.mpr ⟨row, rowMember, itemMember⟩)
  cases item with
  | cnf clause => exact valid
  | fof formula => exact valid.2

def transport (input : NumericInput) (maximum : Usize) :
    Except FangQuantifiedEqualityInput.Error FangQuantifiedEqualityInput.Prepared :=
  FangQuantifiedEqualityInput.transport (legacyInput input) maximum

theorem transport_original {input maximum prepared}
    (success : transport input maximum = .ok prepared) :
    prepared.original = legacyInput input := (FangQuantifiedEqualityInput.transport_runs success).1

theorem transport_tables {input maximum prepared}
    (success : transport input maximum = .ok prepared) :
    FangEqualityBridge.ValidReservation prepared.reservation ∧
    prepared.reservation.original_predicates.val.map (fun value => value.val) = input.predicates.map Prod.snd ∧
    prepared.reservation.equality.val = input.predicates.length ∧
    prepared.reservation.equality.val < maximum.val ∧
    prepared.signature.functions.val.map (fun value => value.val) = input.functions.map Prod.snd ∧
    prepared.signature.predicates.val.map (fun value => value.val) = input.predicates.map Prod.snd ++ [2] := by
  simpa only [legacyInput] using FangQuantifiedEqualityInput.transport_tables success

theorem transport_models {input maximum prepared}
    (success : transport input maximum = .ok prepared) {D : Type} {model : Interpretation D}
    (holds : NamedQuantified.NumericModels model input.declarations) :
    (retained input.declarations).Models model ∧ SignedDeclarationsHold model prepared.declarations.val := by
  have meaning := (FangQuantifiedEqualityInput.transport_models success model).mp (legacy_models holds)
  simpa only [legacyInput, legacy_rows_numeric, NumericInput.declarations] using meaning

theorem retained_below {values : List NumericDeclaration} {limit}
    (below : ∀ value ∈ values, DeclarationBelow limit value) :
    ProblemBelow limit (retained values) := by
  induction values with
  | nil => simp [retained, ProblemBelow]
  | cons value rest ih =>
    have tail := ih (fun item member => below item (List.mem_cons_of_mem _ member))
    cases value with
    | cnf clause =>
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact below (.cnf item) List.mem_cons_self
      · exact tail item member
    | fof formula => exact tail

theorem transport_retained_below {values input maximum prepared}
    (encoded : readInput values = some input) (success : transport input maximum = .ok prepared) :
    ProblemBelow prepared.signature.functions.val.length (retained input.declarations) := by
  obtain ⟨_, _, _, _, functions, _⟩ := transport_tables success
  have count : prepared.signature.functions.val.length = input.functions.length := by
    simpa only [List.length_map] using congrArg List.length functions
  rw [count]
  exact retained_below (readInput_below encoded)

#print axioms Fang.TptpCandidate.FullFof.Integration.legacy_declaration_numeric
#print axioms Fang.TptpCandidate.FullFof.Integration.legacy_rows_numeric
#print axioms Fang.TptpCandidate.FullFof.Integration.legacy_models
#print axioms Fang.TptpCandidate.FullFof.Integration.transport_original
#print axioms Fang.TptpCandidate.FullFof.Integration.transport_tables
#print axioms Fang.TptpCandidate.FullFof.Integration.transport_models
#print axioms Fang.TptpCandidate.FullFof.Integration.retained_below
#print axioms Fang.TptpCandidate.FullFof.Integration.transport_retained_below

end Fang.TptpCandidate.FullFof.Integration
