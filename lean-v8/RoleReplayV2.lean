/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed role tasks over the revision-2 role framer through the accepted signed replay and the version-8 `checkProblem`. The generated distinct-object disequalities enter each task as positive CNF items. -/
import RoleReadV2
import SignedBundleReplay

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Bundle.V2
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-- The generated disequalities mention only nullary IDs of the complete function table. -/
theorem distinct_below {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle tokenize files maximum = .ok bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input) :
    FangQuantifiedPipeline.ProblemBelow input.functions.length (retainedClauses (distinctItems input bundle items)) := by
  have covered := framed_objects_covered framed items (read_tables read)
  have bound : ∀ id ∈ objectIds input bundle items, id < input.functions.length := by
    intro id member
    simp only [objectIds, List.mem_map] at member
    obtain ⟨label, labelMember, rfl⟩ := member
    exact Arity.id_bound (covered label labelMember)
  intro clause member literal literalMember term termMember
  have present := mem_retainedClauses member
  simp only [distinctItems, Coverage.distinctAxioms, List.map_map, List.mem_map, Function.comp_def] at present
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

theorem task_below {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle tokenize files maximum = .ok bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input) {task : List SignedNumeric}
    (fromRows : FromRows input task) :
    FangQuantifiedPipeline.ProblemBelow input.functions.length
      (retainedClauses (task ++ distinctItems input bundle items)) := by
  rw [retainedClauses_append]
  intro clause member
  rcases List.mem_append.mp member with original | generated
  · exact retained_below read fromRows clause original
  · exact distinct_below framed read clause generated

inductive TaskError where
  | read : ReadError → TaskError
  | noGoal
  | cnfGoal
  | goalsPresent
  | replay : Signed.SignedError → TaskError

/-- The task for the conjecture with this index among all selected conjectures, in expansion order; `item` is its bundle identity. -/
def prepareGoal (tokenize : Tokenizer) (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except TaskError BundleGoalPrepared := do
  let read ← (readBundle tokenize files maximumBytes).mapError .read
  let some (before, goal, after) := (Signed.goalSplits read.input)[index]? | .error .noGoal
  let some (item, _) := (goalItems read.bundle read.items)[index]? | .error .noGoal
  let some task := goalTask before goal after | .error .cnfGoal
  let replay ← (Signed.replayTask read.input (task ++ distinctItems read.input read.bundle read.items)
    limits maximumPredicates maximumLiterals).mapError .replay
  pure ⟨item, replay⟩

/-- The satisfiability task, only when no conjecture is selected. -/
def prepareInputs (tokenize : Tokenizer) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except TaskError Signed.SignedPrepared := do
  let read ← (readBundle tokenize files maximumBytes).mapError .read
  if (goalItems read.bundle read.items).isEmpty then
    (Signed.replayTask read.input (inputsTask read.input ++ distinctItems read.input read.bundle read.items)
      limits maximumPredicates maximumLiterals).mapError .replay
  else .error .goalsPresent

theorem prepareGoal_witness {tokenize files maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareGoal tokenize files maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ read before goal after entry task, readBundle tokenize files maximumBytes = .ok read ∧
      (Signed.goalSplits read.input)[index]? = some (before, goal, after) ∧
      (goalItems read.bundle read.items)[index]? = some (prepared.item, entry) ∧
      goalTask before goal after = some task ∧
      Signed.replayTask read.input (task ++ distinctItems read.input read.bundle read.items)
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
theorem prepareGoal_check_entails {tokenize files maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareGoal tokenize files maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    GoalEntailed tokenize files maximumBytes bundleFuel prepared.item := by
  obtain ⟨read, before, goal, after, entry, task, readRun, selected, identified, built, replayRun⟩ :=
    prepareGoal_witness success
  obtain ⟨expanded, _, signed⟩ := readBundle_witness readRun
  have split := (Signed.goalSplits_member (List.mem_of_getElem? selected)).1
  have unsat := replayTask_check_unsat_below
    (task_below expanded.1 signed (goalTask_fromRows split built)) replayRun certificate accepted
  exact goal_item_entailed expanded signed selected identified built unsat

/-- Checker acceptance on the no-goal task proves `ByteUnsatisfiable`; the entry refuses a bundle with a selected conjecture. -/
theorem prepareInputs_check_unsat {tokenize files maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepareInputs tokenize files maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ByteUnsatisfiable tokenize files maximumBytes bundleFuel := by
  obtain ⟨read, readRun, success⟩ := bind_success success
  obtain ⟨expanded, _, signed⟩ := readBundle_witness (mapError_success readRun)
  split at success
  · rename_i empty
    exact unsatisfiable_of_refuted expanded signed (List.isEmpty_iff.mp empty)
      (replayTask_check_unsat_below (task_below expanded.1 signed (inputsTask_fromRows read.input))
        (mapError_success success) certificate accepted)
  · cases success

/-! Version-8 acceptance. -/

inductive AcceptError where
  | task : TaskError → AcceptError
  | certificate : FullFof.Integration.CertificateError → AcceptError

/-- Accepts the certificate for one goal index and returns that goal's bundle item. -/
def acceptsGoal (tokenize : Tokenizer) (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (proof : String) (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except AcceptError Coverage.Item := do
  let prepared ← (prepareGoal tokenize files maximumBytes index limits maximumPredicates maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate
  pure prepared.item

def acceptsInputs (tokenize : Tokenizer) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (proof : String) (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except AcceptError Unit := do
  let prepared ← (prepareInputs tokenize files maximumBytes limits maximumPredicates maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError
    .certificate

theorem acceptsGoal_entails {tokenize files maximumBytes index proof limits maximumPredicates maximumLiterals item}
    (accepted : acceptsGoal tokenize files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok item) :
    GoalEntailed tokenize files maximumBytes bundleFuel item := by
  obtain ⟨prepared, run, rest⟩ := bind_success accepted
  obtain ⟨_, checked, finished⟩ := bind_success rest
  cases Except.ok.inj finished
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareGoal_check_entails (mapError_success run) parsed refuted

theorem acceptsInputs_unsat {tokenize files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsInputs tokenize files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ByteUnsatisfiable tokenize files maximumBytes bundleFuel := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareInputs_check_unsat (mapError_success run) parsed refuted

/-- Theorem endpoint: at least one selected conjecture, and an accepted version-8 certificate for every goal item. -/
theorem acceptsGoals_theorem {tokenize files maximumBytes bundle items limits maximumPredicates maximumLiterals}
    (expanded : Expanded tokenize files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index proof,
      acceptsGoal tokenize files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok pair.1) :
    ByteTheorem tokenize files maximumBytes bundleFuel :=
  byteTheorem_of_entailed expanded nonempty fun pair member => by
    obtain ⟨index, proof, run⟩ := accepted pair member
    exact acceptsGoal_entails run

#print axioms Fang.TptpCandidate.Roles.Bundle.V2.distinct_below
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.task_below
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.prepareGoal_witness
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.prepareGoal_check_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.prepareInputs_check_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.acceptsGoal_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.acceptsInputs_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.acceptsGoals_theorem

end Fang.TptpCandidate.Roles.Bundle.V2
