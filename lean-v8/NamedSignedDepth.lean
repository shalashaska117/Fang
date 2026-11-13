import NamedSigned
import RoleDecoderDepth

open Aeneas Aeneas.Std
namespace Fang.TptpCandidate.Roles.Signed.DepthNamed
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

def decodeSignedLimited (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) :
    Except SignedError (List Bytes.Entry × SignedInput) := do
  let values ← (Bytes.decodeBytesLimitedD limit maxDepth bytes maximumBytes).mapError .input
  match readSigned values with
  | none => .error .nonliteral
  | some input => .ok (values, input)

theorem decodeSignedLimited_witness {limit maxDepth bytes maximumBytes values input}
    (success : decodeSignedLimited limit maxDepth bytes maximumBytes = .ok (values, input)) :
    Bytes.decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok values ∧ readSigned values = some input := by
  obtain ⟨decodedValues, decoded, success⟩ := bind_success success
  rw [Bytes.decodeBytesLimitedD_eq] at decoded
  cases read : readSigned decodedValues with
  | none => simp [read] at success
  | some result =>
    have same : (decodedValues, result) = (values, input) := Except.ok.inj (by simpa only [read] using success)
    cases same
    exact ⟨mapError_success decoded, read⟩

def prepareGoalNamed (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes index : Nat)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except SignedNamedError GoalPrepared := do
  let (_, input) ← (decodeSignedLimited limit maxDepth bytes maximumBytes).mapError .signed
  let some (before, goal, after) := (goalSplits input)[index]? | .error (.signed .noGoal)
  let some task := goalTask before goal after | .error (.signed .cnfGoal)
  let replay ← replayNamedTask input task limits threshold maximumPredicates maximumLiterals
  pure ⟨goal.declaration, replay⟩

def prepareInputsNamed (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Usize) : Except SignedNamedError SignedPrepared := do
  let decoded ← (decodeSignedLimited limit maxDepth bytes maximumBytes).mapError .signed
  if (goalSplits decoded.2).isEmpty then
    replayNamedTask decoded.2 (inputsTask decoded.2) limits threshold maximumPredicates maximumLiterals
  else .error (.signed .goalsPresent)

theorem prepareGoalNamed_witness {limit maxDepth bytes maximumBytes index limits threshold maximumPredicates maximumLiterals
    prepared}
    (success : prepareGoalNamed limit maxDepth bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
      .ok prepared) :
    ∃ values input before goal after task,
      Bytes.decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok values ∧ readSigned values = some input ∧
      (goalSplits input)[index]? = some (before, goal, after) ∧
      goalTask before goal after = some task ∧
      replayNamedTask input task limits threshold maximumPredicates maximumLiterals = .ok prepared.replay ∧
      prepared.goal = goal.declaration := by
  obtain ⟨⟨values, input⟩, decoded, success⟩ := bind_success success
  obtain ⟨decodedRun, read⟩ := decodeSignedLimited_witness (mapError_success decoded)
  cases selected : (goalSplits input)[index]? with
  | none => simp [selected] at success
  | some split =>
    obtain ⟨before, goal, after⟩ := split
    cases built : goalTask before goal after with
    | none => simp [selected, built] at success
    | some task =>
      simp only [selected, built] at success
      obtain ⟨replay, replayRun, success⟩ := bind_success success
      cases Except.ok.inj success
      exact ⟨values, input, before, goal, after, task, decodedRun, read, selected, built, replayRun, rfl⟩

/-- `prepareGoalLimited_check_entails` with naming. -/
theorem prepareGoalNamed_check_entails {limit maxDepth bytes maximumBytes index limits threshold maximumPredicates
    maximumLiterals prepared}
    (success : prepareGoalNamed limit maxDepth bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    ∃ values, Bytes.ByteParsed bytes maximumBytes values ∧ Bytes.Closed values ∧
      prepared.goal ∈ Roles.goals (Bytes.source values) ∧
      ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
        Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
          Bytes.sentence model prepared.goal.original := by
  obtain ⟨values, input, before, goal, after, task, decoded, read, selected, built, replayRun, goalSame⟩ :=
    prepareGoalNamed_witness success
  obtain ⟨split, role⟩ := goalSplits_member (List.mem_of_getElem? selected)
  have closed := Bytes.decodeUpToD_closed decoded
  have unsat := replayNamedTask_check_unsat read (goalTask_fromRows split built) replayRun certificate accepted
  obtain ⟨_, _, _, sources⟩ := readSigned_exact read
  refine ⟨values, Bytes.decodeUpToD_grammar decoded, closed, ?_, ?_⟩
  · rw [goalSame, ← sources, split]
    exact Roles.goal_member.mpr ⟨List.mem_map_of_mem (f := RoleRow.declaration) (by simp), role⟩
  · rw [goalSame]
    exact goalTask_refuted_entails read closed split built unsat

/-- `prepareInputsLimited_check_unsat` with naming. -/
theorem prepareInputsNamed_check_unsat {limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals
    prepared}
    (success : prepareInputsNamed limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximumBytes := by
  obtain ⟨⟨values, input⟩, decodedRun, success⟩ := bind_success success
  obtain ⟨decoded, read⟩ := decodeSignedLimited_witness (mapError_success decodedRun)
  split at success
  · rename_i empty
    have noGoals : Roles.goals (Bytes.source values) = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro goal member
      obtain ⟨before, row, after, split, role, rfl⟩ := goal_row read member
      have inside : (before, row, after) ∈ goalSplits input := by
        simp only [goalSplits, List.mem_filter, decide_eq_true_eq]
        exact ⟨mem_splits.mpr split, role⟩
      rw [List.isEmpty_iff.mp empty] at inside
      cases inside
    have closed := Bytes.decodeUpToD_closed decoded
    rw [Bytes.parsed_inputs_satisfiable (Bytes.decodeUpToD_grammar decoded) closed noGoals]
    rintro ⟨D, inhabited, model, holds⟩
    exact replayNamedTask_check_unsat read (inputsTask_fromRows input) success certificate accepted
      ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates,
        (inputsTask_models read closed (model_toNumeric model _ _)).mpr holds⟩
  · cases success

/-! Version-8 acceptance over the limited decoder with naming. -/

def acceptsGoalNamed (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except SignedNamedAcceptError Unit := do
  let prepared ← (prepareGoalNamed limit maxDepth bytes maximumBytes index limits threshold maximumPredicates
    maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate

def acceptsInputsNamed (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except SignedNamedAcceptError Unit := do
  let prepared ← (prepareInputsNamed limit maxDepth bytes maximumBytes limits threshold maximumPredicates
    maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities
    prepared.predicateArities proof).mapError .certificate

theorem acceptsGoalNamed_replay {limit maxDepth bytes maximumBytes index proof limits threshold maximumPredicates
    maximumLiterals}
    (accepted : acceptsGoalNamed limit maxDepth bytes maximumBytes index proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoalNamed limit maxDepth bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧
      ∃ parsed, Fang.Equality.Ordered.check prepared.replay.problem parsed = .ok () := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact ⟨prepared, mapError_success run, parsed, refuted⟩

/-- `acceptsGoalLimited_entails` with naming, for every threshold. -/
theorem acceptsGoalNamed_entails {limit maxDepth bytes maximumBytes index proof limits threshold maximumPredicates
    maximumLiterals}
    (accepted : acceptsGoalNamed limit maxDepth bytes maximumBytes index proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoalNamed limit maxDepth bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧
      ∃ values, Bytes.ByteParsed bytes maximumBytes values ∧ Bytes.Closed values ∧
        prepared.goal ∈ Roles.goals (Bytes.source values) ∧
        ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
            Bytes.sentence model prepared.goal.original := by
  obtain ⟨prepared, run, parsed, refuted⟩ := acceptsGoalNamed_replay accepted
  exact ⟨prepared, run, prepareGoalNamed_check_entails run parsed refuted⟩

/-- `acceptsGoalsLimited_theorem` with naming, for every threshold. -/
theorem acceptsGoalsNamed_theorem {limit maxDepth bytes maximumBytes values limits threshold maximumPredicates
    maximumLiterals}
    (decoded : Bytes.decodeBytesLimitedD limit maxDepth bytes maximumBytes = .ok values)
    (nonempty : Roles.goals (Bytes.source values) ≠ [])
    (accepted : ∀ goal ∈ Roles.goals (Bytes.source values), ∃ index prepared proof,
      prepareGoalNamed limit maxDepth bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧
      prepared.goal = goal ∧
      acceptsGoalNamed limit maxDepth bytes maximumBytes index proof limits threshold maximumPredicates maximumLiterals =
        .ok ()) :
    BytesTheorem bytes maximumBytes := by
  rw [Bytes.decodeBytesLimitedD_eq] at decoded
  have parsed := Bytes.decodeUpToD_grammar decoded
  have closed := Bytes.decodeUpToD_closed decoded
  refine ⟨values, parsed, closed, nonempty, ?_⟩
  intro D inhabited goal member model premisesHold
  obtain ⟨index, prepared, proof, run, same, checked⟩ := accepted goal member
  obtain ⟨other, otherRun, certificate, refuted⟩ := acceptsGoalNamed_replay checked
  have equal : other = prepared := Except.ok.inj (otherRun.symm.trans run)
  subst equal
  obtain ⟨otherValues, otherParsed, _, _, entails⟩ := prepareGoalNamed_check_entails run certificate refuted
  have sources := Bytes.byteParsed_source_unique otherParsed parsed
  rw [sources, same] at entails
  exact entails D inhabited model premisesHold

/-- `acceptsInputsLimited_unsat` with naming, for every threshold. -/
theorem acceptsInputsNamed_unsat {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsInputsNamed limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximumBytes := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareInputsNamed_check_unsat (mapError_success run) parsed refuted


theorem decodeSignedLimited_accepted (limit bytes maximumBytes) :
    decodeSignedLimited limit 64 bytes maximumBytes = Signed.decodeSignedLimited limit bytes maximumBytes := by
  unfold decodeSignedLimited Signed.decodeSignedLimited
  rw [Bytes.decodeBytesLimitedD_accepted]
  rfl

theorem prepareGoalNamed_accepted (limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals) :
    prepareGoalNamed limit 64 bytes maximumBytes index limits threshold maximumPredicates maximumLiterals = Signed.prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals := by
  unfold prepareGoalNamed Signed.prepareGoalNamed
  rw [decodeSignedLimited_accepted]
  rfl

theorem prepareInputsNamed_accepted (limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals) :
    prepareInputsNamed limit 64 bytes maximumBytes limits threshold maximumPredicates maximumLiterals = Signed.prepareInputsNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals := by
  unfold prepareInputsNamed Signed.prepareInputsNamed
  rw [decodeSignedLimited_accepted]

theorem acceptsGoalNamed_accepted (limit bytes maximumBytes index proof limits threshold maximumPredicates maximumLiterals) :
    acceptsGoalNamed limit 64 bytes maximumBytes index proof limits threshold maximumPredicates maximumLiterals = Signed.acceptsGoalNamed limit bytes maximumBytes index proof limits threshold maximumPredicates maximumLiterals := by
  unfold acceptsGoalNamed Signed.acceptsGoalNamed
  rw [prepareGoalNamed_accepted]

theorem acceptsInputsNamed_accepted (limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals) :
    acceptsInputsNamed limit 64 bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = Signed.acceptsInputsNamed limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals := by
  unfold acceptsInputsNamed Signed.acceptsInputsNamed
  rw [prepareInputsNamed_accepted]

end Fang.TptpCandidate.Roles.Signed.DepthNamed
