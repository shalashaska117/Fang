/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed bundle replay with naming. The task construction, goal identities and
   endpoint meanings are those of RoleReplayLimit; the replay uses named blocks.
   The results hold for every threshold and every sound frame. -/
import NamedSigned
import RoleReplayLimit

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Bundle.V3.Named
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

inductive TaskError where
  | read : V2.ReadError -> TaskError
  | noGoal : TaskError
  | cnfGoal : TaskError
  | goalsPresent : TaskError
  | replay : Signed.SignedNamedError -> TaskError

inductive AcceptError where
  | task : TaskError -> AcceptError
  | certificate : FullFof.Integration.CertificateError -> AcceptError

def prepareGoal (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except TaskError BundleGoalPrepared := do
  let read ← (readBundle frame files maximumBytes).mapError .read
  let some (before, goal, after) := (Signed.goalSplits read.input)[index]? | .error .noGoal
  let some (item, _) := (goalItems read.bundle read.items)[index]? | .error .noGoal
  let some task := goalTask before goal after | .error .cnfGoal
  let replay ← (Signed.replayNamedTask read.input (task ++ V2.distinctItems read.input read.bundle read.items)
    limits threshold maximumPredicates maximumLiterals).mapError .replay
  pure ⟨item, replay⟩

/-- The satisfiability task, only when no conjecture is selected. -/
def prepareInputs (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except TaskError Signed.SignedPrepared := do
  let read ← (readBundle frame files maximumBytes).mapError .read
  if (goalItems read.bundle read.items).isEmpty then
    (Signed.replayNamedTask read.input (inputsTask read.input ++ V2.distinctItems read.input read.bundle read.items)
      limits threshold maximumPredicates maximumLiterals).mapError .replay
  else .error .goalsPresent

theorem prepareGoal_witness {frame files maximumBytes index limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareGoal frame files maximumBytes index limits threshold maximumPredicates maximumLiterals = .ok prepared) :
    ∃ read before goal after entry task, readBundle frame files maximumBytes = .ok read ∧
      (Signed.goalSplits read.input)[index]? = some (before, goal, after) ∧
      (goalItems read.bundle read.items)[index]? = some (prepared.item, entry) ∧
      goalTask before goal after = some task ∧
      Signed.replayNamedTask read.input (task ++ V2.distinctItems read.input read.bundle read.items)
        limits threshold maximumPredicates maximumLiterals = .ok prepared.replay := by
  obtain ⟨read, readRun, success⟩ := bind_success success
  cases selected : (Signed.goalSplits read.input)[index]? with
  | none => simp [selected] at success
  | some split =>
    obtain ⟨before, goal, after⟩ := split
    cases identified : (goalItems read.bundle read.items)[index]? with
    | none => simp [selected, identified] at success
    | some pair =>
      obtain ⟨item, entry⟩ := pair
      cases built : goalTask before goal after with
      | none => simp [selected, identified, built] at success
      | some task =>
        simp only [selected, identified, built] at success
        obtain ⟨replay, replayRun, success⟩ := bind_success success
        cases Except.ok.inj success
        exact ⟨read, before, goal, after, entry, task, mapError_success readRun, selected, identified, built,
          mapError_success replayRun⟩

/-- Checker acceptance on one goal task proves that goal, identified by its bundle item. -/
theorem prepareGoal_check_entails {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes index limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareGoal frame files maximumBytes index limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    GoalEntailed frame files maximumBytes bundleFuel prepared.item := by
  obtain ⟨read, before, goal, after, entry, task, readRun, selected, identified, built, replayRun⟩ :=
    prepareGoal_witness success
  obtain ⟨expanded, _, signed⟩ := readBundle_witness readRun
  have split := (Signed.goalSplits_member (List.mem_of_getElem? selected)).1
  have unsat := Signed.replayNamedTask_check_unsat_below
    (task_below (frameSound expanded.1) signed (goalTask_fromRows split built)) replayRun certificate accepted
  exact goal_item_entailed frameSound expanded signed selected identified built unsat

/-- Checker acceptance on the no-goal task proves `ByteUnsatisfiable`; the entry refuses a bundle with a selected conjecture. -/
theorem prepareInputs_check_unsat {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareInputs frame files maximumBytes limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ByteUnsatisfiable frame files maximumBytes bundleFuel := by
  obtain ⟨read, readRun, success⟩ := bind_success success
  obtain ⟨expanded, _, signed⟩ := readBundle_witness (mapError_success readRun)
  split at success
  · rename_i empty
    exact unsatisfiable_of_refuted frameSound expanded signed (List.isEmpty_iff.mp empty)
      (Signed.replayNamedTask_check_unsat_below (task_below (frameSound expanded.1) signed (inputsTask_fromRows read.input))
        (mapError_success success) certificate accepted)
  · cases success

/-! Version-8 acceptance. -/

/-- Accepts the certificate for one goal index and returns that goal's bundle item. -/
def acceptsGoal (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (proof : String) (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except AcceptError Coverage.Item := do
  let prepared ← (prepareGoal frame files maximumBytes index limits threshold maximumPredicates maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate
  pure prepared.item

def acceptsInputs (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (proof : String) (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except AcceptError Unit := do
  let prepared ← (prepareInputs frame files maximumBytes limits threshold maximumPredicates maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError
    .certificate


theorem acceptsGoal_entails {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes index proof limits threshold maximumPredicates maximumLiterals item}
    (accepted : acceptsGoal frame files maximumBytes index proof limits threshold maximumPredicates maximumLiterals = .ok item) :
    GoalEntailed frame files maximumBytes bundleFuel item := by
  obtain ⟨prepared, run, rest⟩ := bind_success accepted
  obtain ⟨_, checked, finished⟩ := bind_success rest
  cases Except.ok.inj finished
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareGoal_check_entails frameSound (mapError_success run) parsed refuted

theorem acceptsInputs_unsat {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsInputs frame files maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok ()) :
    ByteUnsatisfiable frame files maximumBytes bundleFuel := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareInputs_check_unsat frameSound (mapError_success run) parsed refuted

/-- Theorem endpoint: at least one selected conjecture, and an accepted version-8 certificate for every goal item. -/
theorem acceptsGoals_theorem {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes bundle items limits threshold maximumPredicates maximumLiterals}
    (expanded : Expanded frame files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index proof,
      acceptsGoal frame files maximumBytes index proof limits threshold maximumPredicates maximumLiterals = .ok pair.1) :
    ByteTheorem frame files maximumBytes bundleFuel :=
  byteTheorem_of_entailed expanded nonempty fun pair member => by
    obtain ⟨index, proof, run⟩ := accepted pair member
    exact acceptsGoal_entails frameSound run


theorem acceptsGoalLimited_entails {files maximumBytes index proof limits threshold maximumPredicates maximumLiterals item}
    (accepted : acceptsGoal limited files maximumBytes index proof limits threshold maximumPredicates maximumLiterals = .ok item) :
    GoalEntailed limitedSpecification files maximumBytes bundleFuel item := by
  rw [limited_eq] at accepted
  exact acceptsGoal_entails limitedSpecification_sound accepted

theorem acceptsInputsLimited_unsat {files maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsInputs limited files maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok ()) :
    ByteUnsatisfiable limitedSpecification files maximumBytes bundleFuel := by
  rw [limited_eq] at accepted
  exact acceptsInputs_unsat limitedSpecification_sound accepted

/-- Theorem endpoint of the limited checker: at least one selected conjecture, and an accepted version-8 certificate for every goal item. -/
theorem acceptsGoalsLimited_theorem {files maximumBytes bundle items limits threshold maximumPredicates maximumLiterals}
    (expanded : Expanded limitedSpecification files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index proof,
      acceptsGoal limited files maximumBytes index proof limits threshold maximumPredicates maximumLiterals = .ok pair.1) :
    ByteTheorem limitedSpecification files maximumBytes bundleFuel :=
  byteTheorem_of_entailed expanded nonempty fun pair member => by
    obtain ⟨index, proof, run⟩ := accepted pair member
    exact acceptsGoalLimited_entails run


end Fang.TptpCandidate.Roles.Bundle.V3.Named
