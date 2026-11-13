/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The signed version-8 entries over the limited decoder, with naming. The task
   replay is `replayTask` with the named blocks and the final checks of the
   expanded entry in place of the plain blocks and conversion; the goal and
   inputs entries and their endpoints are those of `RoleDecoderLimit` with that
   replay, and they state the same conclusions for every threshold. -/
import NamedCore
import RoleDecoderLimit

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Signed
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

inductive SignedNamedError where
  | signed : SignedError → SignedNamedError
  | named : FullFof.Integration.Named.NamedError → SignedNamedError

/-- `replayTask` with naming: the same transport, encoding and Skolemization,
    then the named blocks, assembly and the final checks and conversion. -/
def replayNamedTask (input : SignedInput) (task : List SignedNumeric) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Usize) : Except SignedNamedError SignedPrepared := do
  let encoded ← (Integration.transport (tables input) maximumPredicates).mapError
    (fun error => .signed (.transport error))
  let declarations ← (encodeSigned (signedFormulas task)).mapError (fun error => .signed (.width error))
  let declarations ← (FangOriginalInput.checkedSlice declarations).mapError (fun error => .signed (.width error))
  let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    declarations encoded.signature limits.skolem) .skolem).mapError (fun error => .signed (.preprocessing error))
  let first ← (Integration.Named.firstNamed encoded.reservation.equality).mapError .named
  let named ← (Integration.Named.replayNamedBlocks limits threshold first.val first transformed.formulas.val).mapError
    (fun error => .signed (.preprocessing error))
  let ordinary ← (FangOriginalReplay.assemble (taskDeclarations task) named.1).mapError
    (fun error => .signed (.preprocessing error))
  let problem ← (Integration.Named.finishWith (taskDeclarations task) encoded.reservation first named ordinary
    maximumPredicates maximumLiterals).mapError .named
  pure ⟨input, task, problem, transformed.signature.functions.val.map (fun value => value.val),
    input.predicates.map Prod.snd ++ named.2.2.map (fun value => value.val)⟩

/-- Naming preserves the refutation argument for tasks with bounded retained terms. -/
theorem replayNamedTask_check_unsat_below {input task limits threshold maximumPredicates maximumLiterals prepared}
    (below : FangQuantifiedPipeline.ProblemBelow input.functions.length (retainedClauses task))
    (success : replayNamedTask input task limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ TaskSatisfiable input task := by
  unfold replayNamedTask at success
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨declarations, declarationsRun, success⟩ := bind_success success
  obtain ⟨slice, sliceRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨first, firstRun, success⟩ := bind_success success
  obtain ⟨named, namedRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  obtain ⟨finished, finishRun, success⟩ := bind_success success
  cases Except.ok.inj success
  rintro ⟨D, nonempty, model, holds⟩
  let : Nonempty D := nonempty
  obtain ⟨valid, _, slot, _, functions, _⟩ := Integration.transport_tables (mapError_success inputRun)
  obtain ⟨retainedHold, signedHold⟩ := taskModels_parts holds
  have signedDeclarations : FangQuantifiedPipeline.SignedDeclarationsHold
      (FullFof.reserve input.predicates.length model) slice.val := by
    rw [FangOriginalInput.checkedSlice_values (mapError_success sliceRun)]
    exact (signed_hold (encodeSigned_related (mapError_success declarationsRun)) _).mpr signedHold
  have reservedHolds :
      (retainedClauses task).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model) ∧
      FangQuantifiedPipeline.SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model) slice.val := by
    rw [slot, ← Integration.reserve_interpretation]
    exact ⟨retainedHold, signedDeclarations⟩
  have count : encoded.signature.functions.val.length = input.functions.length := by
    simpa only [List.length_map, tables] using congrArg List.length functions
  have bounded : FangQuantifiedPipeline.ProblemBelow encoded.signature.functions.val.length
      (retainedClauses task) := by
    rw [count]
    exact below
  have skolemSuccess := FangOriginalReplay.observe_success (mapError_success skolemRun)
  obtain ⟨skolemized, preserved, meaning⟩ := FangSkolemCore.skolemize_problem_independent_meaning
    skolemSuccess (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model)
  have retainedModels : (Fang.QuantifiedCertificate.retained (taskDeclarations task)).Models skolemized := by
    rw [retained_taskDeclarations]
    exact (FangQuantifiedPipeline.problem_preserved preserved _ bounded).mpr reservedHolds.1
  exact Integration.Named.named_unsat valid (mapError_success firstRun) (mapError_success namedRun)
    (mapError_success assemblyRun) (mapError_success finishRun) model skolemized preserved
    (fun formula member =>
      ⟨⟨_, FangQuantifiedPipeline.skolemize_problem_scoped skolemSuccess formula member⟩,
        (FangSkolemCore.skolemize_problem_output skolemSuccess formula member).1,
        fun valuation => (meaning valuation).mp
          (fun declaration present => reservedHolds.2 declaration present valuation) formula member⟩)
    retainedModels certificate accepted

/-- `replayTask_check_unsat` with naming. -/
theorem replayNamedTask_check_unsat {values input task limits threshold maximumPredicates maximumLiterals prepared}
    (read : readSigned values = some input) (fromRows : FromRows input task)
    (success : replayNamedTask input task limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ TaskSatisfiable input task :=
  replayNamedTask_check_unsat_below (retained_below read fromRows) success certificate accepted

/-! The limited goal and inputs entries with naming. -/

def prepareGoalNamed (limit : Nat) (bytes : List UInt8) (maximumBytes index : Nat)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except SignedNamedError GoalPrepared := do
  let (_, input) ← (decodeSignedLimited limit bytes maximumBytes).mapError .signed
  let some (before, goal, after) := (goalSplits input)[index]? | .error (.signed .noGoal)
  let some task := goalTask before goal after | .error (.signed .cnfGoal)
  let replay ← replayNamedTask input task limits threshold maximumPredicates maximumLiterals
  pure ⟨goal.declaration, replay⟩

def prepareInputsNamed (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Usize) : Except SignedNamedError SignedPrepared := do
  let decoded ← (decodeSignedLimited limit bytes maximumBytes).mapError .signed
  if (goalSplits decoded.2).isEmpty then
    replayNamedTask decoded.2 (inputsTask decoded.2) limits threshold maximumPredicates maximumLiterals
  else .error (.signed .goalsPresent)

theorem prepareGoalNamed_witness {limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals
    prepared}
    (success : prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
      .ok prepared) :
    ∃ values input before goal after task,
      Bytes.decodeBytesUpTo limit bytes maximumBytes = .ok values ∧ readSigned values = some input ∧
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
theorem prepareGoalNamed_check_entails {limit bytes maximumBytes index limits threshold maximumPredicates
    maximumLiterals prepared}
    (success : prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
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
  have closed := Bytes.decodeUpTo_closed decoded
  have unsat := replayNamedTask_check_unsat read (goalTask_fromRows split built) replayRun certificate accepted
  obtain ⟨_, _, _, sources⟩ := readSigned_exact read
  refine ⟨values, Bytes.decodeUpTo_grammar decoded, closed, ?_, ?_⟩
  · rw [goalSame, ← sources, split]
    exact Roles.goal_member.mpr ⟨List.mem_map_of_mem (f := RoleRow.declaration) (by simp), role⟩
  · rw [goalSame]
    exact goalTask_refuted_entails read closed split built unsat

/-- `prepareInputsLimited_check_unsat` with naming. -/
theorem prepareInputsNamed_check_unsat {limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals
    prepared}
    (success : prepareInputsNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
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
    have closed := Bytes.decodeUpTo_closed decoded
    rw [Bytes.parsed_inputs_satisfiable (Bytes.decodeUpTo_grammar decoded) closed noGoals]
    rintro ⟨D, inhabited, model, holds⟩
    exact replayNamedTask_check_unsat read (inputsTask_fromRows input) success certificate accepted
      ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates,
        (inputsTask_models read closed (model_toNumeric model _ _)).mpr holds⟩
  · cases success

/-! Version-8 acceptance over the limited decoder with naming. -/

inductive SignedNamedAcceptError where
  | replay : SignedNamedError → SignedNamedAcceptError
  | certificate : FullFof.Integration.CertificateError → SignedNamedAcceptError

def acceptsGoalNamed (limit : Nat) (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except SignedNamedAcceptError Unit := do
  let prepared ← (prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates
    maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate

def acceptsInputsNamed (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except SignedNamedAcceptError Unit := do
  let prepared ← (prepareInputsNamed limit bytes maximumBytes limits threshold maximumPredicates
    maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities
    prepared.predicateArities proof).mapError .certificate

theorem acceptsGoalNamed_replay {limit bytes maximumBytes index proof limits threshold maximumPredicates
    maximumLiterals}
    (accepted : acceptsGoalNamed limit bytes maximumBytes index proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧
      ∃ parsed, Fang.Equality.Ordered.check prepared.replay.problem parsed = .ok () := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact ⟨prepared, mapError_success run, parsed, refuted⟩

/-- `acceptsGoalLimited_entails` with naming, for every threshold. -/
theorem acceptsGoalNamed_entails {limit bytes maximumBytes index proof limits threshold maximumPredicates
    maximumLiterals}
    (accepted : acceptsGoalNamed limit bytes maximumBytes index proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧
      ∃ values, Bytes.ByteParsed bytes maximumBytes values ∧ Bytes.Closed values ∧
        prepared.goal ∈ Roles.goals (Bytes.source values) ∧
        ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
            Bytes.sentence model prepared.goal.original := by
  obtain ⟨prepared, run, parsed, refuted⟩ := acceptsGoalNamed_replay accepted
  exact ⟨prepared, run, prepareGoalNamed_check_entails run parsed refuted⟩

/-- `acceptsGoalsLimited_theorem` with naming, for every threshold. -/
theorem acceptsGoalsNamed_theorem {limit bytes maximumBytes values limits threshold maximumPredicates
    maximumLiterals}
    (decoded : Bytes.decodeBytesLimited limit bytes maximumBytes = .ok values)
    (nonempty : Roles.goals (Bytes.source values) ≠ [])
    (accepted : ∀ goal ∈ Roles.goals (Bytes.source values), ∃ index prepared proof,
      prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧
      prepared.goal = goal ∧
      acceptsGoalNamed limit bytes maximumBytes index proof limits threshold maximumPredicates maximumLiterals =
        .ok ()) :
    BytesTheorem bytes maximumBytes := by
  rw [Bytes.decodeBytesLimited_eq] at decoded
  have parsed := Bytes.decodeUpTo_grammar decoded
  have closed := Bytes.decodeUpTo_closed decoded
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
theorem acceptsInputsNamed_unsat {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsInputsNamed limit bytes maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximumBytes := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareInputsNamed_check_unsat (mapError_success run) parsed refuted

end Fang.TptpCandidate.Roles.Signed
