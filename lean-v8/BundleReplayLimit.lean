/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Version-8 acceptance over a sealed bundle for any sound frame function. `bundleNumeric`, `prepareBundle` and `acceptsBundle` are the `BundleV8` definitions with the frame as a parameter, and with framer revision 2 as the frame they are those definitions. For every sound frame, acceptance refutes the bundle under `FramerLimit.ByteBundleSatisfiable` for that frame. The hashed framer at any limit is sound and equal to the list framer with that limit, so `acceptsBundleHashed_refuted` restates `acceptsBundleFast_refuted` for every limit; `limited` is the hashed framer at `Fang.NativeLimits.declarationLimit`, the frame of the native checker. -/
import BundleFramerHashed
import BundleFastFramer
import NativeLimits

namespace Fang.TptpCandidate.FullFof.Coverage.BundleLimit

open Aeneas.Std
open Fang.QuantifiedCertificate FangQuantifiedPipeline
open FangQuantifiedEqualityReplay (bind_success mapError_success)
open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2 (wellShaped objectNames NamedSeparated)
open Fang.TptpCandidate.FullFof.Coverage.FramerLimit (Frame FrameSound ByteBundleSatisfiable frameBundle
  frameBundleHashed)
open Fang.TptpCandidate.FullFof.Coverage.BundleV8 (bundleFuel withGenerated withGenerated_declarations
  withGenerated_tables objectIds BundleError BundleReplayError BundleAcceptError replayFrom replayFrom_check_unsat)

/-- `BundleV8.bundleNumeric` with the frame as a parameter. -/
def bundleNumeric (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat) :
    Except BundleError NumericInput :=
  match frame files maximumBytes with
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

theorem bundleNumeric_revision_two : bundleNumeric FramerV2.frameBundle = BundleV8.bundleNumeric := rfl

theorem bundleNumeric_witness {frame : Frame} {files : List (Key × List UInt8)} {maximumBytes : Nat}
    {numeric : NumericInput} (success : bundleNumeric frame files maximumBytes = .ok numeric) :
    ∃ bundle items input, frame files maximumBytes = .ok bundle ∧
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
theorem bundleNumeric_below {frame : Frame} (frameSound : FrameSound frame) {files : List (Key × List UInt8)}
    {maximumBytes : Nat} {numeric : NumericInput} (success : bundleNumeric frame files maximumBytes = .ok numeric) :
    ∀ value ∈ numeric.declarations, DeclarationBelow numeric.functions.length value := by
  obtain ⟨bundle, items, input, framed, _, _, encoded, rfl⟩ := bundleNumeric_witness success
  rw [(withGenerated_tables input _).1, withGenerated_declarations]
  intro value member
  rcases List.mem_append.mp member with original | generated
  · exact readInput_below encoded value original
  · simp only [distinctAxioms, List.mem_map] at generated
    obtain ⟨⟨left, right⟩, present, rfl⟩ := generated
    have ⟨leftMember, rightMember, _⟩ := pairs_mem present
    have covered := FramerLimit.objects_covered (frameSound framed) items encoded
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

/-- A refutation of the bundle's numeric input refutes the bundle under the frame's meaning. -/
theorem bundleNumeric_unsat {frame : Frame} (frameSound : FrameSound frame) {files : List (Key × List UInt8)}
    {maximumBytes : Nat} {numeric : NumericInput} (success : bundleNumeric frame files maximumBytes = .ok numeric)
    (refuted : ¬ numeric.Satisfiable) : ¬ ByteBundleSatisfiable frame files maximumBytes bundleFuel := by
  obtain ⟨bundle, items, input, framed, _, expanded, encoded, rfl⟩ := bundleNumeric_witness success
  refine FramerLimit.byte_bundle_unsat_of_refutation (files := files) (maximum := maximumBytes) frameSound framed
    expanded encoded ?_
  intro satisfiable
  apply refuted
  rw [input_satisfiable, (withGenerated_tables input _).2, withGenerated_declarations]
  exact satisfiable

def prepareBundle (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleReplayError ReplayPrepared := do
  let numeric ← (bundleNumeric frame files maximumBytes).mapError .bundle
  (replayFrom numeric limits maximumPredicates maximumLiterals).mapError .replay

theorem prepareBundle_revision_two : prepareBundle FramerV2.frameBundle = BundleV8.prepareBundle := rfl

/-- `BundleV8.acceptsBundle` with the frame as a parameter. -/
def acceptsBundle (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleAcceptError Unit := do
  let prepared ← (prepareBundle frame files maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

theorem acceptsBundle_revision_two : acceptsBundle FramerV2.frameBundle = BundleV8.acceptsBundle := rfl

/-- Acceptance excludes every model of the bundle under a sound frame, distinct objects separated. -/
theorem acceptsBundle_original_unsat {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ ByteBundleSatisfiable frame files maximumBytes bundleFuel := by
  obtain ⟨prepared, prepareRun, checked⟩ := bind_success accepted
  obtain ⟨numeric, numericRun, replayRun⟩ := bind_success (mapError_success prepareRun)
  obtain ⟨parsed, _, _, _, refuted⟩ := checkProblem_success (mapError_success checked)
  have numericOk := mapError_success numericRun
  exact bundleNumeric_unsat frameSound numericOk
    (replayFrom_check_unsat (bundleNumeric_below frameSound numericOk) (mapError_success replayRun) parsed refuted)

/-- `BundleV8.BundleRefuted` with the frame as a parameter: the bundle frames, is well shaped and
    expands, and has no model under the frame's meaning. -/
def BundleRefuted (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes fuel : Nat) : Prop :=
  (∃ bundle items, frame files maximumBytes = .ok bundle ∧ wellShaped bundle fuel = true ∧
    expand bundle fuel = .ok items) ∧ ¬ ByteBundleSatisfiable frame files maximumBytes fuel

theorem bundleRefuted_revision_two : BundleRefuted FramerV2.frameBundle = BundleV8.BundleRefuted := rfl

theorem acceptsBundle_refuted {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    BundleRefuted frame files maximumBytes bundleFuel := by
  refine ⟨?_, acceptsBundle_original_unsat frameSound accepted⟩
  obtain ⟨prepared, prepareRun, _⟩ := bind_success accepted
  obtain ⟨numeric, numericRun, _⟩ := bind_success (mapError_success prepareRun)
  obtain ⟨bundle, items, _, framed, shaped, expanded, _, _⟩ := bundleNumeric_witness (mapError_success numericRun)
  exact ⟨bundle, items, framed, shaped, expanded⟩

/-- The same content with the model quantifier written out. -/
theorem acceptsBundle_no_model {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundle frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ∃ bundle items, frame files maximumBytes = .ok bundle ∧ wellShaped bundle bundleFuel = true ∧
      expand bundle bundleFuel = .ok items ∧
      ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
        Models (source (declarationsOf bundle items)) model →
        ¬ NamedSeparated model (objectNames (declarationsOf bundle items)) := by
  obtain ⟨⟨bundle, items, framed, shaped, expanded⟩, unsat⟩ := acceptsBundle_refuted frameSound accepted
  exact ⟨bundle, items, framed, shaped, expanded, fun D nonempty model models separated =>
    unsat ⟨bundle, items, framed, shaped, expanded, D, nonempty, model, models, separated⟩⟩

/-! Any limit, and the decision-9 instance. -/

/-- Acceptance with the hashed framer at any limit refutes the bundle under the list framer with that limit. -/
theorem acceptsBundleHashed_refuted (limit : Nat) {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundle (frameBundleHashed limit) files maximumBytes proof limits maximumPredicates
      maximumLiterals = .ok ()) :
    BundleRefuted (frameBundle limit) files maximumBytes bundleFuel := by
  rw [FramerLimit.frameBundleHashed_eq] at accepted
  exact acceptsBundle_refuted (FramerLimit.frameBundle_sound limit) accepted

/-- At 1,000 formulas per file the hashed entry is the entry of the earlier native checker. -/
theorem acceptsBundle_hashed_accepted (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle (frameBundleHashed 1000) files maximumBytes proof limits maximumPredicates maximumLiterals =
      BundleV8.acceptsBundleFast files maximumBytes proof limits maximumPredicates maximumLiterals := by
  rw [FramerLimit.frameBundleHashed_accepted, acceptsBundle_revision_two, BundleV8.acceptsBundleFast_eq]

/-- The frame the limited native checker runs. -/
def limited : Frame := frameBundleHashed Fang.NativeLimits.declarationLimit

/-- The frame its meaning is stated over. -/
def limitedSpecification : Frame := frameBundle Fang.NativeLimits.declarationLimit

theorem limited_eq : limited = limitedSpecification := FramerLimit.frameBundleHashed_eq _

theorem limitedSpecification_sound : FrameSound limitedSpecification := FramerLimit.frameBundle_sound _

theorem acceptsBundleLimited_refuted {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundle limited files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    BundleRefuted limitedSpecification files maximumBytes bundleFuel :=
  acceptsBundleHashed_refuted Fang.NativeLimits.declarationLimit accepted

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.bundleNumeric_revision_two
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.bundleNumeric_witness
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.bundleNumeric_below
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.bundleNumeric_unsat
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.prepareBundle_revision_two
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.acceptsBundle_revision_two
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.acceptsBundle_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.bundleRefuted_revision_two
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.acceptsBundle_refuted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.acceptsBundle_no_model
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.acceptsBundleHashed_refuted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.acceptsBundle_hashed_accepted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.limited_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.limitedSpecification_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.acceptsBundleLimited_refuted

end Fang.TptpCandidate.FullFof.Coverage.BundleLimit
