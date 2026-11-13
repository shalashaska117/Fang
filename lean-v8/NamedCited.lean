/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed role tasks that replay only the premises a certificate cites. The whole bundle is read, framed and expanded as for the other entries, and the goal is chosen among the selected conjectures of the whole expansion; the task, its tables, its distinct-object disequalities and the replay are then built over the kept items only: the cited items and the goal's item, in expansion order. The meanings proved are the ones of the full entries, `GoalEntailed` and `ByteUnsatisfiable`, by monotonicity (`RoleCitedRead.lean`). The entries refuse a citation that is not an expanded premise (goal task) or positive input (inputs task); soundness does not depend on that check. -/
import RoleCitedRead
import NamedRoleBundle

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Bundle.V3.Named
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

inductive CitedError where
  | task : TaskError → CitedError
  /-- A cited item that is not an expanded record with an allowed role. -/
  | citation : Coverage.Item → CitedError

/-- The first cited item that is not an expanded record whose role passes `allowed`. -/
def badCitation (bundle : RoleBundle) (items : List Coverage.Item) (allowed : Role → Bool) :
    List Coverage.Item → Option Coverage.Item
  | [] => none
  | item :: rest =>
    let kept := items.contains item && match roleStatementAt bundle item with
      | some (.formula value) => allowed value.role
      | _ => false
    if kept then badCitation bundle items allowed rest else some item

/-- The task for the conjecture with this index among the selected conjectures of the whole expansion, over the kept items. -/
def prepareGoalCited (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (cited : List Coverage.Item) (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except CitedError BundleGoalPrepared := do
  let read ← (readBundle frame files maximumBytes).mapError (.task ∘ .read)
  match badCitation read.bundle read.items isPremise cited with
  | some bad => .error (.citation bad)
  | none =>
    let some (item, _) := (goalItems read.bundle read.items)[index]? | .error (.task .noGoal)
    let kept := keptItems read.items cited (some item)
    let some input := readSigned (entriesOf read.bundle kept) | .error (.task (.read .nonliteral))
    let position := (goalItems read.bundle kept).findIdx fun pair => pair.1 == item
    match (goalItems read.bundle kept)[position]? with
    | none => .error (.task .noGoal)
    | some (keptItem, _) =>
      if keptItem = item then
        let some (before, goal, after) := (Signed.goalSplits input)[position]? | .error (.task .noGoal)
        let some task := goalTask before goal after | .error (.task .cnfGoal)
        let replay ← (Signed.replayNamedTask input (task ++ V2.distinctItems input read.bundle kept)
          limits threshold maximumPredicates maximumLiterals).mapError (.task ∘ .replay)
        pure ⟨item, replay⟩
      else .error (.task .noGoal)

/-- The satisfiability task over the kept items, only when the whole expansion selects no conjecture. -/
def prepareInputsCited (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (cited : List Coverage.Item) (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except CitedError Signed.SignedPrepared := do
  let read ← (readBundle frame files maximumBytes).mapError (.task ∘ .read)
  match badCitation read.bundle read.items isPositiveInput cited with
  | some bad => .error (.citation bad)
  | none =>
    if (goalItems read.bundle read.items).isEmpty then
      let kept := keptItems read.items cited none
      match readSigned (entriesOf read.bundle kept) with
      | none => .error (.task (.read .nonliteral))
      | some input =>
        (Signed.replayNamedTask input (inputsTask input ++ V2.distinctItems input read.bundle kept)
          limits threshold maximumPredicates maximumLiterals).mapError (.task ∘ .replay)
    else .error (.task .goalsPresent)

theorem prepareGoalCited_witness {frame files maximumBytes index cited limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareGoalCited frame files maximumBytes index cited limits threshold maximumPredicates maximumLiterals =
      .ok prepared) :
    ∃ (read : BundleRead) (entry : Bytes.Entry) (input : SignedInput) (position : Nat) (before : List RoleRow)
      (goal : RoleRow) (after : List RoleRow) (keptEntry : Bytes.Entry) (task : List SignedNumeric),
      readBundle frame files maximumBytes = .ok read ∧
      (goalItems read.bundle read.items)[index]? = some (prepared.item, entry) ∧
      readSigned (entriesOf read.bundle (keptItems read.items cited (some prepared.item))) = some input ∧
      (goalItems read.bundle (keptItems read.items cited (some prepared.item)))[position]? =
        some (prepared.item, keptEntry) ∧
      (Signed.goalSplits input)[position]? = some (before, goal, after) ∧
      goalTask before goal after = some task ∧
      Signed.replayNamedTask input (task ++ V2.distinctItems input read.bundle (keptItems read.items cited (some prepared.item)))
        limits threshold maximumPredicates maximumLiterals = .ok prepared.replay := by
  unfold prepareGoalCited at success
  obtain ⟨read, readRun, success⟩ := bind_success success
  cases bad : badCitation read.bundle read.items isPremise cited with
  | some item => simp [bad] at success
  | none =>
    simp only [bad] at success
    cases identified : (goalItems read.bundle read.items)[index]? with
    | none => simp [identified] at success
    | some pair =>
      obtain ⟨item, entry⟩ := pair
      simp only [identified] at success
      cases readKept : readSigned (entriesOf read.bundle (keptItems read.items cited (some item))) with
      | none => simp [readKept] at success
      | some input =>
        simp only [readKept] at success
        generalize positionEq : (goalItems read.bundle (keptItems read.items cited (some item))).findIdx
          (fun pair => pair.1 == item) = position at success
        cases located : (goalItems read.bundle (keptItems read.items cited (some item)))[position]? with
        | none => simp [located] at success
        | some keptPair =>
          obtain ⟨keptItem, keptEntry⟩ := keptPair
          simp only [located] at success
          by_cases same : keptItem = item
          · rw [ite_eq_left_of_eq_true _ _ (eq_true same)] at success
            rw [same] at located
            cases selected : (Signed.goalSplits input)[position]? with
            | none => simp [selected] at success
            | some split =>
              obtain ⟨before, goal, after⟩ := split
              simp only [selected] at success
              cases built : goalTask before goal after with
              | none => simp [built] at success
              | some task =>
                simp only [built] at success
                obtain ⟨replay, replayRun, success⟩ := bind_success success
                cases Except.ok.inj success
                exact ⟨read, entry, input, position, before, goal, after, keptEntry, task,
                  mapError_success readRun, identified, readKept, located, selected, built,
                  mapError_success replayRun⟩
          · rw [ite_eq_right_of_eq_false _ _ (eq_false same)] at success
            cases success

theorem prepareInputsCited_witness {frame files maximumBytes cited limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareInputsCited frame files maximumBytes cited limits threshold maximumPredicates maximumLiterals =
      .ok prepared) :
    ∃ (read : BundleRead) (input : SignedInput), readBundle frame files maximumBytes = .ok read ∧
      goalItems read.bundle read.items = [] ∧
      readSigned (entriesOf read.bundle (keptItems read.items cited none)) = some input ∧
      Signed.replayNamedTask input (inputsTask input ++ V2.distinctItems input read.bundle (keptItems read.items cited none))
        limits threshold maximumPredicates maximumLiterals = .ok prepared := by
  unfold prepareInputsCited at success
  obtain ⟨read, readRun, success⟩ := bind_success success
  cases bad : badCitation read.bundle read.items isPositiveInput cited with
  | some item => simp [bad] at success
  | none =>
    simp only [bad] at success
    split at success
    · rename_i empty
      cases readKept : readSigned (entriesOf read.bundle (keptItems read.items cited none)) with
      | none => simp [readKept] at success
      | some input =>
        simp only [readKept] at success
        exact ⟨read, input, mapError_success readRun, List.isEmpty_iff.mp empty, readKept,
          mapError_success success⟩
    · cases success

/-- Checker acceptance on a cited goal task proves the goal from all premises of the whole expansion. -/
theorem prepareGoalCited_check_entails {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes index cited limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareGoalCited frame files maximumBytes index cited limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    GoalEntailed frame files maximumBytes bundleFuel prepared.item := by
  obtain ⟨read, entry, input, position, before, goal, after, keptEntry, task, readRun, identified, readKept,
    located, selected, built, replayRun⟩ := prepareGoalCited_witness success
  obtain ⟨expanded, _, _⟩ := readBundle_witness readRun
  have sound := frameSound expanded.1
  have sub := keptItems_sublist read.items cited (some prepared.item)
  have split := (Signed.goalSplits_member (List.mem_of_getElem? selected)).1
  have unsat := Signed.replayNamedTask_check_unsat_below
    (task_below sound readKept (goalTask_fromRows split built)) replayRun certificate accepted
  have holds := goal_holds_of_refuted_lifted sound sub readKept split built unsat
  have declared : goal.declaration = entryDeclaration keptEntry := by
    have chosen : ((splits input.rows).filter (fun split => decide (split.2.1.role = .conjecture)))[position]? =
        some (before, goal, after) := selected
    have mapped := congrArg (fun list => list[position]?) (goal_rows_items readKept)
    simp only [List.getElem?_map, chosen, located, Option.map_some, Option.some.injEq] at mapped
    exact mapped
  have sameEntry : keptEntry = entry := by
    have first := V2.goalItems_entry (List.mem_of_getElem? located)
    have second := V2.goalItems_entry (List.mem_of_getElem? identified)
    rw [first] at second
    simpa using second
  subst sameEntry
  refine ⟨read.bundle, read.items, keptEntry, expanded, List.mem_of_getElem? identified, ?_⟩
  intro D inhabited model separated premisesHold
  have goalHolds := holds D inhabited model separated premisesHold
  rw [declared] at goalHolds
  exact goalHolds

/-- Checker acceptance on a cited inputs task proves `ByteUnsatisfiable` of the whole expansion. -/
theorem prepareInputsCited_check_unsat {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes cited limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareInputsCited frame files maximumBytes cited limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ByteUnsatisfiable frame files maximumBytes bundleFuel := by
  obtain ⟨read, input, readRun, empty, readKept, replayRun⟩ := prepareInputsCited_witness success
  obtain ⟨expanded, _, _⟩ := readBundle_witness readRun
  have sound := frameSound expanded.1
  have sub := keptItems_sublist read.items cited none
  have unsat := Signed.replayNamedTask_check_unsat_below
    (task_below sound readKept (inputsTask_fromRows input)) replayRun certificate accepted
  exact ⟨read.bundle, read.items, expanded, empty, inputs_fail_of_refuted_lifted sound sub readKept unsat⟩

/-! Version-8 acceptance. -/

inductive CitedAcceptError where
  | task : CitedError → CitedAcceptError
  | certificate : FullFof.Integration.CertificateError → CitedAcceptError

def acceptsGoalCited (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (cited : List Coverage.Item) (proof : String) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Usize) : Except CitedAcceptError Coverage.Item := do
  let prepared ← (prepareGoalCited frame files maximumBytes index cited limits threshold maximumPredicates
    maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate
  pure prepared.item

def acceptsInputsCited (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (cited : List Coverage.Item) (proof : String) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Usize) : Except CitedAcceptError Unit := do
  let prepared ← (prepareInputsCited frame files maximumBytes cited limits threshold maximumPredicates
    maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError
    .certificate

theorem acceptsGoalCited_entails {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals item}
    (accepted : acceptsGoalCited frame files maximumBytes index cited proof limits threshold maximumPredicates
      maximumLiterals = .ok item) :
    GoalEntailed frame files maximumBytes bundleFuel item := by
  obtain ⟨prepared, run, rest⟩ := bind_success accepted
  obtain ⟨_, checked, finished⟩ := bind_success rest
  cases Except.ok.inj finished
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareGoalCited_check_entails frameSound (mapError_success run) parsed refuted

theorem acceptsInputsCited_unsat {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsInputsCited frame files maximumBytes cited proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ByteUnsatisfiable frame files maximumBytes bundleFuel := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareInputsCited_check_unsat frameSound (mapError_success run) parsed refuted

/-- Theorem endpoint: at least one selected conjecture, and an accepted certificate for every goal item, each with its own citations. -/
theorem acceptsGoalsCited_theorem {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes bundle items limits threshold maximumPredicates maximumLiterals}
    (expanded : Expanded frame files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index cited proof,
      acceptsGoalCited frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals =
        .ok pair.1) :
    ByteTheorem frame files maximumBytes bundleFuel :=
  byteTheorem_of_entailed expanded nonempty fun pair member => by
    obtain ⟨index, cited, proof, run⟩ := accepted pair member
    exact acceptsGoalCited_entails frameSound run

/-! The decision-9 instance. -/

theorem acceptsGoalCitedLimited_entails {files maximumBytes index cited proof limits threshold maximumPredicates
    maximumLiterals item}
    (accepted : acceptsGoalCited limited files maximumBytes index cited proof limits threshold maximumPredicates
      maximumLiterals = .ok item) :
    GoalEntailed limitedSpecification files maximumBytes bundleFuel item := by
  rw [limited_eq] at accepted
  exact acceptsGoalCited_entails limitedSpecification_sound accepted

theorem acceptsInputsCitedLimited_unsat {files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsInputsCited limited files maximumBytes cited proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ByteUnsatisfiable limitedSpecification files maximumBytes bundleFuel := by
  rw [limited_eq] at accepted
  exact acceptsInputsCited_unsat limitedSpecification_sound accepted

/-- Theorem endpoint of the limited checker with citations. -/
theorem acceptsGoalsCitedLimited_theorem {files maximumBytes bundle items limits threshold maximumPredicates maximumLiterals}
    (expanded : Expanded limitedSpecification files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index cited proof,
      acceptsGoalCited limited files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals =
        .ok pair.1) :
    ByteTheorem limitedSpecification files maximumBytes bundleFuel :=
  byteTheorem_of_entailed expanded nonempty fun pair member => by
    obtain ⟨index, cited, proof, run⟩ := accepted pair member
    exact acceptsGoalCitedLimited_entails run

/-! Control: citing every expanded item keeps today's entries, so the kept read is the whole read. -/

theorem citedEntries_every (bundle : RoleBundle) (items : List Coverage.Item) (extra : Option Coverage.Item) :
    entriesOf bundle (keptItems items items extra) = entriesOf bundle items := by
  rw [keptItems_all]

theorem citedRead_every {frame : Frame} {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat}
    {read : BundleRead} (success : readBundle frame files maximumBytes = .ok read) (extra : Option Coverage.Item) :
    readSigned (entriesOf read.bundle (keptItems read.items read.items extra)) = some read.input := by
  rw [citedEntries_every]
  exact (readBundle_witness success).2.2

end Fang.TptpCandidate.Roles.Bundle.V3.Named
