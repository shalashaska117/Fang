/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed role tasks over any sound frame function, through the accepted signed replay and the version-8 `checkProblem`. The read, the tasks and the entries are the revision-2 ones with `V2.frameBundle tokenize` replaced by a frame parameter. The instance for the hashed framer with the shared declaration limit of the limits record states its meanings over the list framer `frameBundle declarationLimit V2.gated`. -/
import RoleMeaningLimit
import NativeLimits

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Bundle.V3
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-- Expansion errors precede the shape check, and the mode check follows it, as in the revision-2 read. -/
def readBundle (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat) :
    Except V2.ReadError BundleRead :=
  match frame files maximumBytes with
  | .error problem => .error (.frame problem)
  | .ok bundle =>
    match Coverage.expand (forget bundle) bundleFuel with
    | .error problem => .error (.expand problem)
    | .ok items =>
      if Coverage.FramerV2.wellShaped (forget bundle) bundleFuel then
        if Bytes.modesValid (entriesOf bundle items) then
          match readSigned (entriesOf bundle items) with
          | none => .error .nonliteral
          | some input => .ok ⟨bundle, items, input⟩
        else .error .modes
      else .error .shape

/-- With the revision-2 role framer as the frame, the read is the revision-2 one. -/
theorem readBundle_revision_two (tokenize : V2.Tokenizer) :
    readBundle (V2.frameBundle tokenize) = V2.readBundle tokenize := rfl

theorem readBundle_witness {frame : Frame} {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat}
    {read : BundleRead} (success : readBundle frame files maximumBytes = .ok read) :
    Expanded frame files maximumBytes bundleFuel read.bundle read.items ∧
      Bytes.modesValid (entriesOf read.bundle read.items) = true ∧
      readSigned (entriesOf read.bundle read.items) = some read.input := by
  unfold readBundle at success
  split at success
  · cases success
  · rename_i bundle framed
    split at success
    · cases success
    · rename_i items expanded
      split at success
      · rename_i shaped
        split at success
        · rename_i modes
          split at success
          · cases success
          · rename_i input signed
            cases success
            exact ⟨⟨framed, shaped, expanded⟩, modes, signed⟩
        · cases success
      · cases success

/-- The generated disequalities mention only nullary IDs of the complete function table. -/
theorem distinct_below {bundle : RoleBundle} (sound : SoundBundle bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input) :
    FangQuantifiedPipeline.ProblemBelow input.functions.length (retainedClauses (V2.distinctItems input bundle items)) := by
  have covered := objects_covered sound items (read_tables read)
  have bound : ∀ id ∈ V2.objectIds input bundle items, id < input.functions.length := by
    intro id member
    simp only [V2.objectIds, List.mem_map] at member
    obtain ⟨label, labelMember, rfl⟩ := member
    exact Arity.id_bound (covered label labelMember)
  intro clause member literal literalMember term termMember
  have present := mem_retainedClauses member
  simp only [V2.distinctItems, Coverage.distinctAxioms, List.map_map, List.mem_map, Function.comp_def] at present
  obtain ⟨⟨left, right⟩, pairMember, shape⟩ := present
  simp only [Coverage.disequality, positive, SignedNumeric.cnf.injEq] at shape
  subst shape
  obtain ⟨leftMember, rightMember, _⟩ := Coverage.pairs_mem pairMember
  simp only [List.mem_singleton] at literalMember
  subst literalMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at termMember
  rcases termMember with rfl | rfl
  · simp only [Fang.QuantifiedFOF.Skolem.TermBelow]
    exact ⟨bound left leftMember, by simp⟩
  · simp only [Fang.QuantifiedFOF.Skolem.TermBelow]
    exact ⟨bound right rightMember, by simp⟩

theorem task_below {bundle : RoleBundle} (sound : SoundBundle bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input) {task : List SignedNumeric}
    (fromRows : FromRows input task) :
    FangQuantifiedPipeline.ProblemBelow input.functions.length
      (retainedClauses (task ++ V2.distinctItems input bundle items)) := by
  rw [retainedClauses_append]
  intro clause member
  rcases List.mem_append.mp member with original | generated
  · exact retained_below read fromRows clause original
  · exact distinct_below sound read clause generated

/-- The task for the conjecture with this index among all selected conjectures, in expansion order; `item` is its bundle identity. -/
def prepareGoal (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except V2.TaskError BundleGoalPrepared := do
  let read ← (readBundle frame files maximumBytes).mapError .read
  let some (before, goal, after) := (Signed.goalSplits read.input)[index]? | .error .noGoal
  let some (item, _) := (goalItems read.bundle read.items)[index]? | .error .noGoal
  let some task := goalTask before goal after | .error .cnfGoal
  let replay ← (Signed.replayTask read.input (task ++ V2.distinctItems read.input read.bundle read.items)
    limits maximumPredicates maximumLiterals).mapError .replay
  pure ⟨item, replay⟩

/-- The satisfiability task, only when no conjecture is selected. -/
def prepareInputs (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except V2.TaskError Signed.SignedPrepared := do
  let read ← (readBundle frame files maximumBytes).mapError .read
  if (goalItems read.bundle read.items).isEmpty then
    (Signed.replayTask read.input (inputsTask read.input ++ V2.distinctItems read.input read.bundle read.items)
      limits maximumPredicates maximumLiterals).mapError .replay
  else .error .goalsPresent

theorem prepareGoal_witness {frame files maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareGoal frame files maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ read before goal after entry task, readBundle frame files maximumBytes = .ok read ∧
      (Signed.goalSplits read.input)[index]? = some (before, goal, after) ∧
      (goalItems read.bundle read.items)[index]? = some (prepared.item, entry) ∧
      goalTask before goal after = some task ∧
      Signed.replayTask read.input (task ++ V2.distinctItems read.input read.bundle read.items)
        limits maximumPredicates maximumLiterals = .ok prepared.replay := by
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
    {files maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareGoal frame files maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    GoalEntailed frame files maximumBytes bundleFuel prepared.item := by
  obtain ⟨read, before, goal, after, entry, task, readRun, selected, identified, built, replayRun⟩ :=
    prepareGoal_witness success
  obtain ⟨expanded, _, signed⟩ := readBundle_witness readRun
  have split := (Signed.goalSplits_member (List.mem_of_getElem? selected)).1
  have unsat := replayTask_check_unsat_below
    (task_below (frameSound expanded.1) signed (goalTask_fromRows split built)) replayRun certificate accepted
  exact goal_item_entailed frameSound expanded signed selected identified built unsat

/-- Checker acceptance on the no-goal task proves `ByteUnsatisfiable`; the entry refuses a bundle with a selected conjecture. -/
theorem prepareInputs_check_unsat {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepareInputs frame files maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ByteUnsatisfiable frame files maximumBytes bundleFuel := by
  obtain ⟨read, readRun, success⟩ := bind_success success
  obtain ⟨expanded, _, signed⟩ := readBundle_witness (mapError_success readRun)
  split at success
  · rename_i empty
    exact unsatisfiable_of_refuted frameSound expanded signed (List.isEmpty_iff.mp empty)
      (replayTask_check_unsat_below (task_below (frameSound expanded.1) signed (inputsTask_fromRows read.input))
        (mapError_success success) certificate accepted)
  · cases success

/-! Version-8 acceptance. -/

/-- Accepts the certificate for one goal index and returns that goal's bundle item. -/
def acceptsGoal (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (proof : String) (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except V2.AcceptError Coverage.Item := do
  let prepared ← (prepareGoal frame files maximumBytes index limits maximumPredicates maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate
  pure prepared.item

def acceptsInputs (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (proof : String) (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except V2.AcceptError Unit := do
  let prepared ← (prepareInputs frame files maximumBytes limits maximumPredicates maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError
    .certificate

/-- With the revision-2 role framer as the frame, the goal entry is the revision-2 one. -/
theorem acceptsGoal_revision_two (tokenize : V2.Tokenizer) :
    acceptsGoal (V2.frameBundle tokenize) = V2.acceptsGoal tokenize := rfl

theorem acceptsInputs_revision_two (tokenize : V2.Tokenizer) :
    acceptsInputs (V2.frameBundle tokenize) = V2.acceptsInputs tokenize := rfl

theorem acceptsGoal_entails {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes index proof limits maximumPredicates maximumLiterals item}
    (accepted : acceptsGoal frame files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok item) :
    GoalEntailed frame files maximumBytes bundleFuel item := by
  obtain ⟨prepared, run, rest⟩ := bind_success accepted
  obtain ⟨_, checked, finished⟩ := bind_success rest
  cases Except.ok.inj finished
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareGoal_check_entails frameSound (mapError_success run) parsed refuted

theorem acceptsInputs_unsat {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsInputs frame files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ByteUnsatisfiable frame files maximumBytes bundleFuel := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareInputs_check_unsat frameSound (mapError_success run) parsed refuted

/-- Theorem endpoint: at least one selected conjecture, and an accepted version-8 certificate for every goal item. -/
theorem acceptsGoals_theorem {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes bundle items limits maximumPredicates maximumLiterals}
    (expanded : Expanded frame files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index proof,
      acceptsGoal frame files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok pair.1) :
    ByteTheorem frame files maximumBytes bundleFuel :=
  byteTheorem_of_entailed expanded nonempty fun pair member => by
    obtain ⟨index, proof, run⟩ := accepted pair member
    exact acceptsGoal_entails frameSound run

/-! The decision-9 instance: the hashed framer with the shared declaration limit. The meanings are stated over the list framer with the gated tokenizer, which `frameBundleHashed_eq` proves equal to it. -/

/-- The frame the limited native checker runs. -/
def limited : Frame := frameBundleHashed Fang.NativeLimits.declarationLimit

/-- The frame its meanings are stated over. -/
def limitedSpecification : Frame := frameBundle Fang.NativeLimits.declarationLimit V2.gated

theorem limited_eq : limited = limitedSpecification := frameBundleHashed_eq _

theorem limitedSpecification_sound : FrameSound limitedSpecification := frameBundle_sound _ _

theorem acceptsGoalLimited_entails {files maximumBytes index proof limits maximumPredicates maximumLiterals item}
    (accepted : acceptsGoal limited files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok item) :
    GoalEntailed limitedSpecification files maximumBytes bundleFuel item := by
  rw [limited_eq] at accepted
  exact acceptsGoal_entails limitedSpecification_sound accepted

theorem acceptsInputsLimited_unsat {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsInputs limited files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ByteUnsatisfiable limitedSpecification files maximumBytes bundleFuel := by
  rw [limited_eq] at accepted
  exact acceptsInputs_unsat limitedSpecification_sound accepted

/-- Theorem endpoint of the limited checker: at least one selected conjecture, and an accepted version-8 certificate for every goal item. -/
theorem acceptsGoalsLimited_theorem {files maximumBytes bundle items limits maximumPredicates maximumLiterals}
    (expanded : Expanded limitedSpecification files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index proof,
      acceptsGoal limited files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok pair.1) :
    ByteTheorem limitedSpecification files maximumBytes bundleFuel :=
  byteTheorem_of_entailed expanded nonempty fun pair member => by
    obtain ⟨index, proof, run⟩ := accepted pair member
    exact acceptsGoalLimited_entails run

/-- At the revision-2 limit of 1,000 formulas per file, the hashed framer is the revision-2 framer over the gated tokenizer. -/
theorem frameBundleHashed_accepted : frameBundleHashed 1000 = V2.frameBundle V2.gated := by
  rw [frameBundleHashed_eq]
  funext files maximum
  exact frameBundle_accepted V2.gated files maximum

/-- So the hashed entries at that limit are the entries the role-v4 checker runs, through `acceptsGoalFast_eq`. -/
theorem acceptsGoal_hashed_accepted : acceptsGoal (frameBundleHashed 1000) = V2.acceptsGoal V2.gated := by
  rw [frameBundleHashed_accepted]
  rfl

theorem acceptsInputs_hashed_accepted : acceptsInputs (frameBundleHashed 1000) = V2.acceptsInputs V2.gated := by
  rw [frameBundleHashed_accepted]
  rfl

#print axioms Fang.TptpCandidate.Roles.Bundle.V3.readBundle_revision_two
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.readBundle_witness
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.distinct_below
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.task_below
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.prepareGoal_witness
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.prepareGoal_check_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.prepareInputs_check_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsGoal_revision_two
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsInputs_revision_two
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsGoal_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsInputs_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsGoals_theorem
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.limited_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.limitedSpecification_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsGoalLimited_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsInputsLimited_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsGoalsLimited_theorem
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.frameBundleHashed_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsGoal_hashed_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.acceptsInputs_hashed_accepted

end Fang.TptpCandidate.Roles.Bundle.V3
