/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed role tasks through the actual Reservation, Skolem, removal, clausification and equality conversion calls, ending in the ordered equality checker. -/
import SignedEntry
import ExpandedReplay

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Signed
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-! Every decoded conjecture body is FOF. -/

theorem grammar_keyword {tokens original rest}
    (grammar : CnfBoolean.DeclarationTokens tokens original rest) :
    ∃ keyword more, tokens = keyword :: more ∧
      keyword.kind = .legacy (.lower (FullFof.Grammar.BodyKind original.body)) := by
  cases grammar with
  | declaration keywordKind => exact ⟨_, _, rfl, keywordKind⟩

theorem declaration_goal_fof {seen endOffset tokens value final}
    (success : Bytes.declaration seen endOffset tokens = .ok (value, final))
    (goal : value.role = .conjecture) : ∃ formula, value.original.body = .fof formula := by
  obtain ⟨header, _, _, valid, originalAt, _, _⟩ := Bytes.declaration_witness success
  obtain ⟨keyword, more, shape, kind⟩ := grammar_keyword (CnfBoolean.declaration_sound originalAt).1
  simp only [Bytes.Header.patched, List.cons.injEq] at shape
  obtain ⟨rfl, -⟩ := shape
  simp only [Bytes.invalidGoal, goal, decide_true, Bool.true_and] at valid
  cases bodyShape : value.original.body with
  | fof formula => exact ⟨formula, rfl⟩
  | cnf literals =>
    rw [bodyShape] at kind
    rw [kind] at valid
    simp only [FullFof.Grammar.BodyKind] at valid
    exact absurd valid (by decide)

def GoalsFof (values : List Bytes.Entry) : Prop :=
  ∀ value ∈ values, value.role = .conjecture → ∃ formula, value.original.body = .fof formula

theorem declarations_goals_fof {fuel seen endOffset input values}
    (success : Bytes.declarations fuel seen endOffset input = .ok values) : GoalsFof values := by
  induction fuel generalizing seen input values with
  | zero => simp [Bytes.declarations, FullFof.failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [Bytes.declarations] at success
      subst values
      simp [GoalsFof]
    | cons token rest =>
      unfold Bytes.declarations at success
      simp only [FullFof.failure, Bind.bind, Except.bind, Pure.pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member goal
      rcases List.mem_cons.mp member with rfl | member
      · exact declaration_goal_fof firstAt goal
      · exact ih tailAt value member goal

theorem decode_goals_fof {bytes maximum values}
    (success : Bytes.decodeBytes bytes maximum = .ok values) : GoalsFof values := by
  obtain ⟨_, _, parsed, _⟩ := Bytes.decode_has_tokens success
  exact declarations_goals_fof parsed

theorem readSigned_member {values input} (read : readSigned values = some input)
    {row} (member : row ∈ input.rows) :
    ∃ value ∈ values, row.role = value.role ∧ row.row.original = value.original := by
  cases rowsAt : readRoleRows (FullFof.functionTable (FullFof.source (values.map Bytes.Entry.original)))
      (FullFof.predicateTable (FullFof.source (values.map Bytes.Entry.original))) values with
  | none => simp [readSigned, rowsAt] at read
  | some rows =>
    have same : (⟨FullFof.functionTable (FullFof.source (values.map Bytes.Entry.original)),
        FullFof.predicateTable (FullFof.source (values.map Bytes.Entry.original)), rows⟩ : SignedInput) = input :=
      Option.some.inj (by simpa [readSigned, rowsAt] using read)
    subst input
    obtain ⟨value, present, role, original, _⟩ := readRoleRows_member rowsAt member
    exact ⟨value, present, role, original⟩

/-- For decoded input every conjecture row has its task; no CNF goal remains. -/
theorem goalTask_exists {bytes maximum values input before goal after}
    (decoded : Bytes.decodeBytes bytes maximum = .ok values) (read : readSigned values = some input)
    (split : input.rows = before ++ goal :: after) (role : goal.role = .conjecture) :
    ∃ items, goalTask before goal after = some items := by
  have member : goal ∈ input.rows := by rw [split]; simp
  obtain ⟨value, valueMember, roleSame, originalSame⟩ := readSigned_member read member
  have valueRole : value.role = .conjecture := by rw [← roleSame]; exact role
  obtain ⟨formula, valueBody⟩ := decode_goals_fof decoded value valueMember valueRole
  obtain ⟨body, _, _⟩ := readSigned_row read (Bytes.decode_closed decoded) member
  rw [originalSame, valueBody] at body
  have declarations : goal.row.declarations =
      [.fof (formula.encode input.functions input.predicates formula.variables)] :=
    (Option.some.inj body).symm
  exact ⟨selectBlock isPremise before ++
      .fof false (formula.encode input.functions input.predicates formula.variables) ::
        selectBlock isPremise after,
    by simp [goalTask, negativeGoal, role, declarations]⟩

/-! Layout view of a task: each FOF item consumes one ordered clause block. -/

def taskDeclarations : List SignedNumeric → List NamedQuantified.NumericDeclaration
  | [] => []
  | .cnf clause :: rest => .cnf clause :: taskDeclarations rest
  | .fof _ formula :: rest => .fof formula :: taskDeclarations rest

theorem retained_taskDeclarations (task : List SignedNumeric) :
    Fang.QuantifiedCertificate.retained (taskDeclarations task) = retainedClauses task := by
  induction task with
  | nil => rfl
  | cons item rest ih =>
    cases item <;> simp [taskDeclarations, Fang.QuantifiedCertificate.retained, retainedClauses, ih]

/-! Replay of one signed task. -/

inductive SignedError where
  | input : Fang.TptpCandidate.Error → SignedError
  | nonliteral
  | noGoal
  | cnfGoal
  | goalsPresent
  | transport : FangQuantifiedEqualityInput.Error → SignedError
  | width : FangOriginalInput.Error → SignedError
  | preprocessing : FangOriginalReplay.Error → SignedError
  | conversion : FangQuantifiedEqualityReplay.Conversion.Error → SignedError

/-- The complete tables with no declarations. The accepted `transport` then runs only the width and Reservation calls on them. -/
def tables (input : SignedInput) : Integration.NumericInput := ⟨input.functions, input.predicates, []⟩

structure SignedPrepared where
  input : SignedInput
  task : List SignedNumeric
  problem : Fang.Equality.Problem
  functionArities : List Nat
  predicateArities : List Nat

/-- The same stage sequence and credits as `Integration.prepare`, with the task's signed declarations in place of the axiom-only encoding. -/
def replayTask (input : SignedInput) (task : List SignedNumeric) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except SignedError SignedPrepared := do
  let encoded ← (Integration.transport (tables input) maximumPredicates).mapError .transport
  let declarations ← (encodeSigned (signedFormulas task)).mapError .width
  let declarations ← (FangOriginalInput.checkedSlice declarations).mapError .width
  let transformed ← (FangOriginalReplay.observe (fang_skolem_core.skolemize_problem
    declarations encoded.signature limits.skolem) .skolem).mapError .preprocessing
  let blocks ← (FangOriginalReplay.replayBlocks limits transformed.formulas.val).mapError .preprocessing
  let ordinary ← (FangOriginalReplay.assemble (taskDeclarations task) blocks).mapError .preprocessing
  let equality ← (FangQuantifiedEqualityReplay.Conversion.problem encoded.reservation maximumLiterals
    ordinary).mapError .conversion
  pure ⟨input, task, equality, transformed.signature.functions.val.map (fun value => value.val),
    input.predicates.map Prod.snd⟩

theorem replayTask_witness {input task limits maximumPredicates maximumLiterals prepared}
    (success : replayTask input task limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ encoded declarations slice transformed blocks ordinary,
      Integration.transport (tables input) maximumPredicates = .ok encoded ∧
      encodeSigned (signedFormulas task) = .ok declarations ∧
      slice.val = declarations ∧
      fang_skolem_core.skolemize_problem slice encoded.signature limits.skolem = .ok (.Ok transformed) ∧
      List.Forall₂ FangQuantifiedPipeline.ActualClausificationStep transformed.formulas.val blocks ∧
      Fang.QuantifiedCertificate.MixedLayout (taskDeclarations task) blocks ordinary ∧
      FangQuantifiedEquality.ActualProblemConversion encoded.reservation ordinary prepared.problem ∧
      prepared.input = input ∧ prepared.task = task := by
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨declarations, declarationsRun, success⟩ := bind_success success
  obtain ⟨slice, sliceRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨blocks, blocksRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  obtain ⟨equality, conversionRun, success⟩ := bind_success success
  cases Except.ok.inj success
  exact ⟨encoded, declarations, slice, transformed, blocks, ordinary, mapError_success inputRun,
    mapError_success declarationsRun, FangOriginalInput.checkedSlice_values (mapError_success sliceRun),
    FangOriginalReplay.observe_success (mapError_success skolemRun),
    FangOriginalReplay.replayBlocks_steps (mapError_success blocksRun),
    FangOriginalReplay.assemble_layout (mapError_success assemblyRun),
    FangQuantifiedEqualityReplay.Conversion.problem_actual (mapError_success conversionRun), rfl, rfl⟩

/-- Ordered checker acceptance on a replayed signed task excludes every model of that task, with the reserved slot read as equality. -/
theorem replayTask_check_unsat {values input task limits maximumPredicates maximumLiterals prepared}
    (read : readSigned values = some input) (fromRows : FromRows input task)
    (success : replayTask input task limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ TaskSatisfiable input task := by
  obtain ⟨encoded, declarations, slice, transformed, blocks, ordinary, inputRun, declarationsRun,
    sliceValues, skolemRun, steps, layout, converted, _, _⟩ := replayTask_witness success
  rintro ⟨D, nonempty, model, holds⟩
  let : Nonempty D := nonempty
  obtain ⟨valid, _, slot, _, functions, _⟩ := Integration.transport_tables inputRun
  obtain ⟨retainedHold, signedHold⟩ := taskModels_parts holds
  have signedDeclarations : FangQuantifiedPipeline.SignedDeclarationsHold
      (FullFof.reserve input.predicates.length model) slice.val := by
    rw [sliceValues]
    exact (signed_hold (encodeSigned_related declarationsRun) _).mpr signedHold
  have reservedHolds :
      (retainedClauses task).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model) ∧
      FangQuantifiedPipeline.SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model) slice.val := by
    rw [slot, ← Integration.reserve_interpretation]
    exact ⟨retainedHold, signedDeclarations⟩
  have count : encoded.signature.functions.val.length = input.functions.length := by
    simpa only [List.length_map, tables] using congrArg List.length functions
  have below : FangQuantifiedPipeline.ProblemBelow encoded.signature.functions.val.length
      (retainedClauses task) := by
    rw [count]
    exact retained_below read fromRows
  obtain ⟨extended, preserved, grouped⟩ := FangQuantifiedPipeline.skolem_actual_problem_models skolemRun
    (retainedClauses task) below blocks steps
    (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model)
  have parts := (FangQuantifiedPipeline.models_append extended _ _).mp (grouped.mpr reservedHolds)
  have mixedModel : ordinary.Models extended := by
    apply (Fang.QuantifiedCertificate.mixedLayout_models layout extended).mpr
    rw [retained_taskDeclarations]
    exact parts
  have equalityModel := (FangQuantifiedEquality.actualProblem_models model extended
    encoded.reservation encoded.signature.functions.val.length valid preserved converted).mp mixedModel
  exact Fang.Equality.Ordered.check_unsat prepared.problem certificate accepted
    ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation model extended, equalityModel⟩

/-! Byte entries: one task per original goal, or the no-goal task. -/

def decodeSigned (bytes : List UInt8) (maximumBytes : Nat) :
    Except SignedError (List Bytes.Entry × SignedInput) := do
  let values ← (Bytes.decodeBytes bytes maximumBytes).mapError .input
  match readSigned values with
  | none => .error .nonliteral
  | some input => .ok (values, input)

theorem decodeSigned_witness {bytes maximumBytes values input}
    (success : decodeSigned bytes maximumBytes = .ok (values, input)) :
    Bytes.decodeBytes bytes maximumBytes = .ok values ∧ readSigned values = some input := by
  obtain ⟨decodedValues, decoded, success⟩ := bind_success success
  cases read : readSigned decodedValues with
  | none => simp [read] at success
  | some result =>
    have same : (decodedValues, result) = (values, input) := Except.ok.inj (by simpa only [read] using success)
    cases same
    exact ⟨mapError_success decoded, read⟩

/-- Original conjectures in source order, each with its exact source context. -/
def goalSplits (input : SignedInput) : List (List RoleRow × RoleRow × List RoleRow) :=
  (splits input.rows).filter (fun split => decide (split.2.1.role = .conjecture))

structure GoalPrepared where
  goal : Roles.Declaration Name FullFof.Formula
  replay : SignedPrepared

/-- The task for the original conjecture with the given index among all conjectures. -/
def prepareGoal (bytes : List UInt8) (maximumBytes index : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except SignedError GoalPrepared := do
  let (_, input) ← decodeSigned bytes maximumBytes
  let some (before, goal, after) := (goalSplits input)[index]? | .error .noGoal
  let some task := goalTask before goal after | .error .cnfGoal
  let replay ← replayTask input task limits maximumPredicates maximumLiterals
  pure ⟨goal.declaration, replay⟩

/-- The satisfiability task, only when the input has no original conjecture. -/
def prepareInputs (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except SignedError SignedPrepared := do
  let decoded ← decodeSigned bytes maximumBytes
  if (goalSplits decoded.2).isEmpty then
    replayTask decoded.2 (inputsTask decoded.2) limits maximumPredicates maximumLiterals
  else .error .goalsPresent

theorem prepareGoal_witness {bytes maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ values input before goal after task,
      Bytes.decodeBytes bytes maximumBytes = .ok values ∧ readSigned values = some input ∧
      (goalSplits input)[index]? = some (before, goal, after) ∧
      goalTask before goal after = some task ∧
      replayTask input task limits maximumPredicates maximumLiterals = .ok prepared.replay ∧
      prepared.goal = goal.declaration := by
  obtain ⟨⟨values, input⟩, decoded, success⟩ := bind_success success
  obtain ⟨decodedRun, read⟩ := decodeSigned_witness decoded
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

theorem goalSplits_member {input : SignedInput} {before goal after}
    (member : (before, goal, after) ∈ goalSplits input) :
    input.rows = before ++ goal :: after ∧ goal.role = .conjecture := by
  simp only [goalSplits, List.mem_filter, decide_eq_true_eq] at member
  exact ⟨mem_splits.mp member.1, member.2⟩

/-- Ordered checker acceptance on the prepared task for one original goal proves that the original premises entail that goal, for the independent byte grammar. -/
theorem prepareGoal_check_entails {bytes maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    ∃ values, Bytes.ByteParsed bytes maximumBytes values ∧ Bytes.Closed values ∧
      prepared.goal ∈ Roles.goals (Bytes.source values) ∧
      ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
        Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
          Bytes.sentence model prepared.goal.original := by
  obtain ⟨values, input, before, goal, after, task, decoded, read, selected, built, replayRun, goalSame⟩ :=
    prepareGoal_witness success
  obtain ⟨split, role⟩ := goalSplits_member (List.mem_of_getElem? selected)
  have closed := Bytes.decode_closed decoded
  have unsat := replayTask_check_unsat read (goalTask_fromRows split built) replayRun certificate accepted
  obtain ⟨_, _, _, sources⟩ := readSigned_exact read
  refine ⟨values, Bytes.decode_grammar decoded, closed, ?_, ?_⟩
  · rw [goalSame, ← sources, split]
    exact Roles.goal_member.mpr ⟨List.mem_map_of_mem (f := RoleRow.declaration) (by simp), role⟩
  · rw [goalSame]
    exact goalTask_refuted_entails read closed split built unsat

/-- A refuted task for every original goal proves original-byte entailment of every original conjecture. Without an original conjecture this conclusion is vacuous; `prepareGoals_check_theorem` is the Theorem endpoint. -/
theorem prepareGoals_check_entails_all {bytes maximumBytes values limits maximumPredicates maximumLiterals}
    (decoded : Bytes.decodeBytes bytes maximumBytes = .ok values)
    (refuted : ∀ goal ∈ Roles.goals (Bytes.source values), ∃ index prepared certificate,
      prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      prepared.goal = goal ∧ Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    Bytes.BytesEntailsAll bytes maximumBytes := by
  apply (Bytes.decode_entails_all decoded).mpr
  intro D inhabited goal member model premisesHold
  obtain ⟨index, prepared, certificate, run, same, accepted⟩ := refuted goal member
  obtain ⟨other, parsed, _, _, entails⟩ := prepareGoal_check_entails run certificate accepted
  have sources := Bytes.byteParsed_source_unique parsed (Bytes.decode_grammar decoded)
  rw [sources, same] at entails
  exact entails D inhabited model premisesHold

/-- The statement for SZS Theorem reporting. `BytesEntailsAll` alone is vacuous without an original conjecture, so this one also requires at least one. -/
def BytesTheorem (bytes : List UInt8) (maximum : Nat) : Prop :=
  ∃ values, Bytes.ByteParsed bytes maximum values ∧ Bytes.Closed values ∧
    Roles.goals (Bytes.source values) ≠ [] ∧
    ∀ (D : Type) (_ : Nonempty D), Roles.EntailsAll (Bytes.sentence (D := D)) (Bytes.source values)

theorem bytesTheorem_entails {bytes maximum} (holds : BytesTheorem bytes maximum) :
    Bytes.BytesEntailsAll bytes maximum := by
  obtain ⟨values, parsed, closed, _, entails⟩ := holds
  intro D inhabited
  exact ⟨values, parsed, closed, entails D inhabited⟩

/-- Theorem endpoint: the decoded input has at least one original conjecture, and each one has a prepared task accepted by the ordered checker. -/
theorem prepareGoals_check_theorem {bytes maximumBytes values limits maximumPredicates maximumLiterals}
    (decoded : Bytes.decodeBytes bytes maximumBytes = .ok values)
    (nonempty : Roles.goals (Bytes.source values) ≠ [])
    (refuted : ∀ goal ∈ Roles.goals (Bytes.source values), ∃ index prepared certificate,
      prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      prepared.goal = goal ∧ Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    BytesTheorem bytes maximumBytes :=
  ⟨values, Bytes.decode_grammar decoded, Bytes.decode_closed decoded, nonempty,
    (Bytes.decode_entails_all decoded).mp (prepareGoals_check_entails_all decoded refuted)⟩

/-- Ordered checker acceptance on the no-goal task proves that the accepted positive inputs of the original bytes are unsatisfiable. -/
theorem prepareInputs_check_unsat {bytes maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepareInputs bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximumBytes := by
  obtain ⟨⟨values, input⟩, decodedRun, success⟩ := bind_success success
  obtain ⟨decoded, read⟩ := decodeSigned_witness decodedRun
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
    rw [← inputsTask_satisfiable_iff decoded read noGoals]
    exact replayTask_check_unsat read (inputsTask_fromRows input) success certificate accepted
  · cases success

#print axioms Fang.TptpCandidate.Roles.Signed.grammar_keyword
#print axioms Fang.TptpCandidate.Roles.Signed.declaration_goal_fof
#print axioms Fang.TptpCandidate.Roles.Signed.declarations_goals_fof
#print axioms Fang.TptpCandidate.Roles.Signed.decode_goals_fof
#print axioms Fang.TptpCandidate.Roles.Signed.readSigned_member
#print axioms Fang.TptpCandidate.Roles.Signed.goalTask_exists
#print axioms Fang.TptpCandidate.Roles.Signed.retained_taskDeclarations
#print axioms Fang.TptpCandidate.Roles.Signed.replayTask_witness
#print axioms Fang.TptpCandidate.Roles.Signed.replayTask_check_unsat
#print axioms Fang.TptpCandidate.Roles.Signed.decodeSigned_witness
#print axioms Fang.TptpCandidate.Roles.Signed.prepareGoal_witness
#print axioms Fang.TptpCandidate.Roles.Signed.goalSplits_member
#print axioms Fang.TptpCandidate.Roles.Signed.prepareGoal_check_entails
#print axioms Fang.TptpCandidate.Roles.Signed.prepareGoals_check_entails_all
#print axioms Fang.TptpCandidate.Roles.Signed.bytesTheorem_entails
#print axioms Fang.TptpCandidate.Roles.Signed.prepareGoals_check_theorem
#print axioms Fang.TptpCandidate.Roles.Signed.prepareInputs_check_unsat

end Fang.TptpCandidate.Roles.Signed
