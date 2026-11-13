/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The numeric input of a sealed bundle: framed, shaped and expanded files read
   by the accepted `readInput`, with the generated distinct-object clauses in
   one extra row after every original row. -/
import BundleFramerNodup
import ExpandedBounds

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8

open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2
open Fang.TptpCandidate.FullFof.Integration (NumericInput NumericRow NumericDeclaration readInput
  DeclarationBelow LiteralBelow readInput_below)

/-- Include depth bound: fuel 17 admits the Rust candidate's depth 16. -/
def bundleFuel : Nat := 17

/-- Record carried by the generated row. The accepted transport reads only its
    name, as a label; no source byte or formula of it is used. -/
def generatedRecord : Declaration := ⟨.atom "fang_distinct_objects", .cnf [], 0, 0, 0, 0⟩

/-- Generated clauses as one extra row; with none, the input is unchanged. -/
def withGenerated (input : NumericInput) : List NumericDeclaration → NumericInput
  | [] => input
  | extra@(_ :: _) => { input with rows := input.rows ++ [⟨generatedRecord, extra⟩] }

theorem withGenerated_declarations (input : NumericInput) (extra : List NumericDeclaration) :
    (withGenerated input extra).declarations = input.declarations ++ extra := by
  cases extra with
  | nil => simp [withGenerated]
  | cons first rest =>
    simp [withGenerated, NumericInput.declarations, List.flatMap_append]

theorem withGenerated_tables (input : NumericInput) (extra : List NumericDeclaration) :
    (withGenerated input extra).functions = input.functions ∧
    (withGenerated input extra).predicates = input.predicates := by
  cases extra <;> exact ⟨rfl, rfl⟩

def objectIds (input : NumericInput) (values : List Declaration) : List Nat :=
  (objectNames values).map fun label => Arity.id input.functions (label, 0)

inductive BundleError where
  | frame : Error → BundleError
  | shape
  | expand : Failure → BundleError
  | nonliteral

def bundleNumeric (files : List (Key × List UInt8)) (maximumBytes : Nat) :
    Except BundleError NumericInput :=
  match frameBundle files maximumBytes with
  | .error failure => .error (.frame failure)
  | .ok bundle =>
    -- Expansion errors precede the shape check, as in the Rust candidate.
    match expand bundle bundleFuel with
    | .error failure => .error (.expand failure)
    | .ok items =>
      if wellShaped bundle bundleFuel then
        match readInput (declarationsOf bundle items) with
        | none => .error .nonliteral
        | some input => .ok (withGenerated input
            (distinctAxioms input.predicates.length (objectIds input (declarationsOf bundle items))))
      else .error .shape

theorem bundleNumeric_witness {files : List (Key × List UInt8)} {maximumBytes : Nat}
    {numeric : NumericInput} (success : bundleNumeric files maximumBytes = .ok numeric) :
    ∃ bundle items input, frameBundle files maximumBytes = .ok bundle ∧
      wellShaped bundle bundleFuel = true ∧ expand bundle bundleFuel = .ok items ∧
      readInput (declarationsOf bundle items) = some input ∧
      numeric = withGenerated input
        (distinctAxioms input.predicates.length (objectIds input (declarationsOf bundle items))) := by
  unfold bundleNumeric at success
  split at success
  · cases success
  · rename_i bundle framed
    split at success
    · cases success
    · rename_i items expanded
      split at success
      · rename_i shaped
        split at success
        · cases success
        · rename_i input encoded
          exact ⟨bundle, items, input, framed, shaped, expanded, encoded, (Except.ok.inj success).symm⟩
      · cases success

/-- Every declaration, original or generated, uses only table function IDs. -/
theorem bundleNumeric_below {files : List (Key × List UInt8)} {maximumBytes : Nat}
    {numeric : NumericInput} (success : bundleNumeric files maximumBytes = .ok numeric) :
    ∀ value ∈ numeric.declarations, DeclarationBelow numeric.functions.length value := by
  obtain ⟨bundle, items, input, framed, _, _, encoded, rfl⟩ := bundleNumeric_witness success
  rw [(withGenerated_tables input _).1, withGenerated_declarations]
  intro value member
  rcases List.mem_append.mp member with original | generated
  · exact readInput_below encoded value original
  · simp only [distinctAxioms, List.mem_map] at generated
    obtain ⟨⟨left, right⟩, present, rfl⟩ := generated
    have ⟨leftMember, rightMember, _⟩ := pairs_mem present
    have covered := framed_objects_covered framed items encoded
    have bound (id : Nat) (member : id ∈ objectIds input (declarationsOf bundle items)) :
        id < input.functions.length := by
      obtain ⟨label, labelMember, rfl⟩ := List.mem_map.mp member
      exact Arity.id_bound (covered label labelMember)
    intro literal literalMember
    simp only [List.mem_singleton] at literalMember
    subst literalMember
    intro term termMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at termMember
    rcases termMember with rfl | rfl
    · unfold QuantifiedFOF.Skolem.TermBelow
      exact ⟨bound left leftMember, by simp⟩
    · unfold QuantifiedFOF.Skolem.TermBelow
      exact ⟨bound right rightMember, by simp⟩

/-- A refutation of the bundle's numeric input refutes the sealed bundle. -/
theorem bundleNumeric_unsat {files : List (Key × List UInt8)} {maximumBytes : Nat}
    {numeric : NumericInput} (success : bundleNumeric files maximumBytes = .ok numeric)
    (refuted : ¬ numeric.Satisfiable) : ¬ ByteBundleSatisfiable files maximumBytes bundleFuel := by
  obtain ⟨bundle, items, input, framed, _, expanded, encoded, rfl⟩ := bundleNumeric_witness success
  apply byte_bundle_unsat_of_refutation framed expanded encoded
  intro satisfiable
  apply refuted
  rw [input_satisfiable, (withGenerated_tables input _).2, withGenerated_declarations]
  exact satisfiable

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.withGenerated_declarations
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.withGenerated_tables
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.bundleNumeric_witness
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.bundleNumeric_below
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.bundleNumeric_unsat

end Fang.TptpCandidate.FullFof.Coverage.BundleV8
