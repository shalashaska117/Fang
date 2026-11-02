/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The TSTP document for one original conjecture (SZS Theorem). The signed task
   for the selected goal runs through the same prepare, envelope decoder,
   signature gate and ordered checker as `acceptsGoal`, with the checked clauses
   retained. The document prints every decoded declaration with its original
   role, the negated goal, the SAP group whose parents are the premises and the
   negated goal, and the clause rows, and refuses a text above 16 MiB. The
   product entry `exportGoalDocument` runs the linear lexer and role decoder and
   generates the symbol names and row labels. -/
import SignedEnvelope
import SignedLinear
import ExpandedDocument
import GoalRows

namespace Fang.TptpCandidate.GoalDocument
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.Roles.Numeric Fang.TptpCandidate.Roles.Signed
open Fang.QuantifiedEqualityTstp Fang.TstpText
open FangQuantifiedEqualityReplay (bind_success mapError_success)

structure GoalOutput where
  prepared : GoalPrepared
  certificate : Fang.Equality.Ordered.Certificate
  clauses : List Fang.Equality.Clause

inductive GoalBuildError where
  | replay : SignedError → GoalBuildError
  | certificate : String → GoalBuildError
  | signature
  | inference : Fang.Equality.TraceError → GoalBuildError

def GoalWellFormed (replay : Roles.Signed.SignedPrepared) (certificate : Fang.Equality.Ordered.Certificate) : Bool :=
  replay.problem.all (Fang.EqualityCertificateInput.clauseWellFormed replay.functionArities replay.predicateArities) &&
    Fang.EqualityOrderedCertificateInput.certificateWellFormed replay.functionArities replay.predicateArities certificate

/-- The signed prepare for goal `index`, then the envelope decoder, signature
    gate and ordered step checker of `acceptsGoal`, keeping the checked clauses. -/
def buildGoal (bytes : List UInt8) (maximumBytes index : Nat) (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except GoalBuildError GoalOutput :=
  match prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals with
  | .error reason => .error (.replay reason)
  | .ok prepared =>
    match Integration.decodeV8 proof with
    | .error reason => .error (.certificate reason)
    | .ok certificate =>
      if GoalWellFormed prepared.replay certificate then
        match retain prepared.replay.problem certificate with
        | .error reason => .error (.inference reason)
        | .ok clauses => .ok ⟨prepared, certificate, clauses⟩
      else .error .signature

theorem buildGoal_witness {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (success : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output) :
    prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok output.prepared ∧
      Integration.decodeV8 proof = .ok output.certificate ∧
      GoalWellFormed output.prepared.replay output.certificate = true ∧
      retain output.prepared.replay.problem output.certificate = .ok output.clauses := by
  cases preparedRun : prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals with
  | error reason => simp [buildGoal, preparedRun] at success
  | ok prepared =>
    cases decoded : Integration.decodeV8 proof with
    | error reason => simp [buildGoal, preparedRun, decoded] at success
    | ok certificate =>
      by_cases valid : GoalWellFormed prepared.replay certificate = true
      · cases retained : retain prepared.replay.problem certificate with
        | error reason => simp [buildGoal, preparedRun, decoded, valid, retained] at success
        | ok clauses =>
          simp [buildGoal, preparedRun, decoded, valid, retained] at success
          subst success
          exact ⟨rfl, rfl, valid, retained⟩
      · simp [buildGoal, preparedRun, decoded, valid] at success

theorem buildGoal_check {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (success : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output) :
    Fang.Equality.Ordered.check output.prepared.replay.problem output.certificate = .ok () := by
  rw [← retain_erases, (buildGoal_witness success).2.2.2]
  rfl

/-- A successful goal build is an accepted `acceptsGoal` pair. Only this direction is proved. -/
theorem buildGoal_accepts {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (success : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output) :
    acceptsGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok () := by
  obtain ⟨preparedRun, decoded, wellFormed, _⟩ := buildGoal_witness success
  simp only [GoalWellFormed, Bool.and_eq_true] at wellFormed
  simp [acceptsGoal, Integration.checkProblem, preparedRun, decoded, wellFormed, buildGoal_check success,
    Except.mapError, bind, Except.bind]

/-- Entailment endpoint: the original premises entail the selected original conjecture. -/
theorem buildGoal_entails {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (success : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output) :
    ∃ values, Roles.Bytes.ByteParsed bytes maximumBytes values ∧ Roles.Bytes.Closed values ∧
      output.prepared.goal ∈ Roles.goals (Roles.Bytes.source values) ∧
      ∀ (D : Type) (_ : Nonempty D) (model : Fang.Source.Interpretation D),
        Roles.AllHold (Roles.Bytes.sentence (D := D)) (Roles.premises (Roles.Bytes.source values)) model →
          Roles.Bytes.sentence model output.prepared.goal.original := by
  obtain ⟨prepared, run, entails⟩ := acceptsGoal_entails (buildGoal_accepts success)
  have same : prepared = output.prepared := Except.ok.inj (run.symm.trans (buildGoal_witness success).1)
  subst same
  exact entails

/-! Clause rows. The row theorems take a successful `build`; these
    take a successful `buildGoal` and repeat the same proofs over `retain`. -/

/-- The derivation part reads the prepared problem and the retained rows. The
    original tables are the signed input's complete tables. -/
def expandedOutput (output : GoalOutput) : Expanded.Output :=
  ⟨⟨Roles.Signed.tables output.prepared.replay.input, output.prepared.replay.problem,
    output.prepared.replay.functionArities, output.prepared.replay.predicateArities⟩,
    output.certificate, output.clauses⟩

theorem goal_rows {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (success : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output) :
    Derivation.Checked output.prepared.replay.problem [] (Expanded.rows (expandedOutput output)) ∧
      (Expanded.rows (expandedOutput output)).map Prod.snd = output.clauses := by
  obtain ⟨checkedSteps, _, _, _⟩ := retain_witness (buildGoal_witness success).2.2.2
  obtain ⟨values, checked, sameSteps, sameClauses⟩ := Derivation.checkSteps_rows checkedSteps
  simp only [List.nil_append] at sameClauses
  have paired : Expanded.rows (expandedOutput output) = values := by
    show output.certificate.steps.zip output.clauses = values
    rw [← sameSteps, ← sameClauses, Derivation.zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameClauses⟩

theorem goal_row_checked {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (success : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : Expanded.rows (expandedOutput output) = leading ++ value :: rest) :
    Fang.Equality.Ordered.checkStep output.prepared.replay.problem (leading.map Prod.snd) value.1 = .ok value.2 := by
  have checked := (goal_rows success).1
  rw [position] at checked
  simpa using checked.row

/-- The last retained row is the empty clause. -/
theorem goal_final_row_empty {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (built : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output) :
    ((Expanded.rows (expandedOutput output))[output.certificate.final]?).map Prod.snd = some [] ∧
      output.certificate.final + 1 = (Expanded.rows (expandedOutput output)).length := by
  obtain ⟨_, _, last, empty⟩ := retain_witness (buildGoal_witness built).2.2.2
  have clauses := (goal_rows built).2
  have clausesLength := congrArg List.length clauses
  simp only [List.length_map] at clausesLength
  refine ⟨?_, by rw [clausesLength]; exact last⟩
  rw [← clauses] at empty
  simpa using empty

/-- Each printed clause row follows from its parent rows; an input row from the
    prepared problem, which the group row states. -/
theorem goal_row_local {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (built : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output)
    {leading : List Derivation.Row} {value : Derivation.Row} {rest : List Derivation.Row}
    (position : Expanded.rows (expandedOutput output) = leading ++ value :: rest)
    {names : Fang.QuantifiedEqualityTstp.Body.Names} {named : List EqualitySource.Literal}
    (same : Fang.QuantifiedEqualityTstp.Body.NamedClause names value.2 named)
    {D : Type} (model : Fang.Source.Interpretation D) (label : String)
    (parentsPrinted : ∀ parent ∈ value.1.parents, ∀ row, leading[parent]? = some row →
      ∃ parentNamed, Fang.QuantifiedEqualityTstp.Body.NamedClause names row.2 parentNamed)
    (parents : ∀ parent ∈ value.1.parents, ∀ row, leading[parent]? = some row →
      ∀ parentNamed, Fang.QuantifiedEqualityTstp.Body.NamedClause names row.2 parentNamed →
        (EqualitySource.Clause.mk "" parentNamed).Valid model)
    (group : ∀ index, value.1 = .input index →
      Fang.Equality.models (tableModel names.view model) output.prepared.replay.problem) :
    (EqualitySource.Clause.mk label named).Valid model := by
  rw [Group.namedClause_valid_iff same model label]
  apply Local.step_local (goal_row_checked built position) (tableModel names.view model)
  · intro parent member clause found
    rw [List.getElem?_map] at found
    cases rowAt : leading[parent]? with
    | none => simp [rowAt] at found
    | some row =>
      simp only [rowAt, Option.map_some, Option.some.injEq] at found
      subst clause
      obtain ⟨parentNamed, parentSame⟩ := parentsPrinted parent member row rowAt
      exact (Group.namedClause_valid_iff parentSame model "").mp
        (parents parent member row rowAt parentNamed parentSame)
  · intro index isInput clause found
    exact group index isInput clause (List.mem_iff_getElem?.mpr ⟨index, found⟩)

/-! SAP for the goal task. -/

/-- The model direction of the signed replay: a model of the task gives a model
    of the prepared problem. The chain is the one in `replayTask_check_unsat`,
    stopped before the checker step. -/
theorem replayTask_models {values input task limits maximumPredicates maximumLiterals prepared}
    (read : readSigned values = some input) (fromRows : FromRows input task)
    (success : replayTask input task limits maximumPredicates maximumLiterals = .ok prepared)
    (satisfiable : TaskSatisfiable input task) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D), Fang.Equality.models model prepared.problem := by
  obtain ⟨encoded, declarations, slice, transformed, blocks, ordinary, inputRun, declarationsRun,
    sliceValues, skolemRun, steps, layout, converted, _, _⟩ := replayTask_witness success
  obtain ⟨D, nonempty, model, holds⟩ := satisfiable
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
    simpa only [List.length_map, Roles.Signed.tables] using congrArg List.length functions
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
  exact ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation model extended, equalityModel⟩

/-- Some model of the original premises falsifies the goal, for the independent byte grammar. -/
def GoalCountermodel (bytes : List UInt8) (maximumBytes : Nat)
    (goal : Roles.Declaration Fang.TptpCandidate.Name FullFof.Formula) : Prop :=
  ∃ values, Roles.Bytes.ByteParsed bytes maximumBytes values ∧
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Source.Interpretation D),
      Roles.AllHold (Roles.Bytes.sentence (D := D)) (Roles.premises (Roles.Bytes.source values)) model ∧
        ¬ Roles.Bytes.sentence model goal.original

theorem prepareGoal_models {bytes maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared)
    (countermodel : GoalCountermodel bytes maximumBytes prepared.goal) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.replay.problem := by
  obtain ⟨values, input, before, goal, after, task, decoded, read, selected, built, replayRun, goalSame⟩ :=
    prepareGoal_witness success
  obtain ⟨split, _⟩ := goalSplits_member (List.mem_of_getElem? selected)
  obtain ⟨other, parsed, D, inhabited, model, premisesHold, fails⟩ := countermodel
  have sources := Roles.Bytes.byteParsed_source_unique parsed (Roles.Bytes.decode_grammar decoded)
  rw [sources] at premisesHold
  rw [goalSame] at fails
  have satisfiable := (goalTask_satisfiable_iff read (Roles.Bytes.decode_closed decoded) split built).mpr
    ⟨D, inhabited, model, premisesHold, fails⟩
  exact replayTask_models read (goalTask_fromRows split built) replayRun satisfiable

/-- SAP for the goal task: if some model of the original premises falsifies the
    selected goal, the printed group formula holds in some source model. -/
theorem goal_group_sap {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (built : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output)
    {functions names} (named : Expanded.attach (expandedOutput output) functions = .ok names)
    {formula} (formulaRun : Group.groupFormula names output.prepared.replay.problem = .ok formula)
    (countermodel : GoalCountermodel bytes maximumBytes output.prepared.goal) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨preparedRun, _, wellFormed, _⟩ := buildGoal_witness built
  simp only [GoalWellFormed, Bool.and_eq_true] at wellFormed
  obtain ⟨D, nonempty, model, holds⟩ := prepareGoal_models preparedRun countermodel
  have namedHolds := Expanded.namedModel_models (prepared := ⟨output.prepared.replay.problem,
    output.prepared.replay.functionArities, output.prepared.replay.predicateArities⟩)
    (Expanded.attach_spec named) wellFormed.1 model holds
  exact ⟨D, nonempty, Expanded.namedModel names model,
    ((Group.groupFormula_spec formulaRun).2.2 (Expanded.namedModel names model)).mpr namedHolds⟩

/-- `buildGoal` over the linear lexer and role decoder. -/
def buildGoalLinear (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    Except GoalBuildError GoalOutput :=
  match prepareGoalLinear bytes maximumBytes index limits maximumPredicates maximumLiterals with
  | .error reason => .error (.replay reason)
  | .ok prepared =>
    match Integration.decodeV8 proof with
    | .error reason => .error (.certificate reason)
    | .ok certificate =>
      if GoalWellFormed prepared.replay certificate then
        match retain prepared.replay.problem certificate with
        | .error reason => .error (.inference reason)
        | .ok clauses => .ok ⟨prepared, certificate, clauses⟩
      else .error .signature

theorem buildGoalLinear_eq (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    buildGoalLinear bytes maximumBytes index proof limits maximumPredicates maximumLiterals =
      buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals := by
  unfold buildGoalLinear buildGoal
  rw [prepareGoalLinear_eq]

/-! The negated goal and the countermodel hypothesis. -/

/-- The decoded entry of the selected goal: a FOF conjecture whose formula is the goal. -/
theorem goal_entry {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output values}
    (built : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output)
    (decoded : Roles.Bytes.decodeBytes bytes maximumBytes = .ok values) :
    ∃ entry ∈ values, entry.role = .conjecture ∧ entry.original.name = output.prepared.goal.metadata ∧
      entry.original.body = .fof output.prepared.goal.original := by
  obtain ⟨other, parsed, _, member, _⟩ := buildGoal_entails built
  have sources := Roles.Bytes.byteParsed_source_unique parsed (Roles.Bytes.decode_grammar decoded)
  rw [sources] at member
  obtain ⟨inSource, role⟩ := Roles.goal_member.mp member
  unfold Roles.Bytes.source at inSource
  obtain ⟨entry, present, same⟩ := List.mem_map.mp inSource
  have entryRole : entry.role = .conjecture := by
    rw [← same] at role
    exact role
  obtain ⟨formula, body⟩ := decode_goals_fof decoded entry present entryRole
  refine ⟨entry, present, entryRole, by rw [← same], ?_⟩
  rw [← same]
  show entry.original.body = .fof entry.original.body.formula
  simp only [body, FullFof.Body.formula]

/-- The selected goal is a closed formula. -/
theorem goal_closed {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (built : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output) :
    output.prepared.goal.original.Within [] := by
  obtain ⟨values, _, _, _, _, _, decoded, _⟩ := prepareGoal_witness (buildGoal_witness built).1
  obtain ⟨entry, present, _, _, body⟩ := goal_entry built decoded
  have closed := Roles.Bytes.decode_closed decoded entry present
  rw [body] at closed
  exact closed

/-- The hypothesis of `goal_group_sap` says that some model of the original
    premises makes the formula of the printed negated row true: for the closed
    goal, failure of the goal is truth of its negation (`named_failure_iff`). -/
theorem goalCountermodel_negated {bytes maximumBytes index proof limits maximumPredicates maximumLiterals output}
    (built : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output) :
    GoalCountermodel bytes maximumBytes output.prepared.goal ↔
      ∃ values, Roles.Bytes.ByteParsed bytes maximumBytes values ∧
        ∃ (D : Type) (_ : Nonempty D) (model : Fang.Source.Interpretation D),
          Roles.AllHold (Roles.Bytes.sentence (D := D)) (Roles.premises (Roles.Bytes.source values)) model ∧
            Roles.Bytes.sentence model (.neg output.prepared.goal.original) := by
  have closed := goal_closed built
  constructor
  · rintro ⟨values, parsed, D, inhabited, model, holds, fails⟩
    have := inhabited
    exact ⟨values, parsed, D, inhabited, model, holds, (named_failure_iff model closed).mp fails⟩
  · rintro ⟨values, parsed, D, inhabited, model, holds, negated⟩
    have := inhabited
    exact ⟨values, parsed, D, inhabited, model, holds, (named_failure_iff model closed).mpr negated⟩

/-! The document. -/

/-- The parents of the group row: the premise entries in source order, then the negated goal. -/
def groupParents (values : List Roles.Bytes.Entry) (negatedLabel : String) : List Fang.TptpCandidate.Name :=
  (GoalRows.premiseEntries values).map (fun entry => entry.original.name) ++ [.atom negatedLabel]

/-- The document text of a built goal task and its decoded declarations. -/
def goalDocumentOf (output : GoalOutput) (values : List Roles.Bytes.Entry) (file : String)
    (functions : List Frontend.Symbol) (negatedLabel groupLabel : String) (labels : List String) :
    Except String String := do
  let names ← Expanded.attach (expandedOutput output) functions
  if (GoalRows.goalNames (values.map (fun entry => entry.original.name)) negatedLabel groupLabel labels).Nodup then
    let rows ← values.mapM (GoalRows.entryRow file)
    let negated ← GoalRows.negatedRow negatedLabel output.prepared.goal.metadata output.prepared.goal.original
    let parents ← (groupParents values negatedLabel).mapM Expanded.parentText
    let group ← Expanded.sapRow names output.prepared.replay.problem groupLabel parents
    let rowTexts ← Rows.render names groupLabel labels (Expanded.rows (expandedOutput output))
    Expanded.capText (String.join (rows.map (· ++ "\n")) ++ negated ++ "\n" ++ group ++ String.join rowTexts)
  else .error "export-error: document names are not distinct"

def goalDocument (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) (file : String)
    (functions : List Frontend.Symbol) (negatedLabel groupLabel : String) (labels : List String) :
    Except String String := do
  let output ← (buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals).mapError
    (fun _ => "export-error: the goal task is not accepted")
  let values ← (Roles.Bytes.decodeBytes bytes maximumBytes).mapError (fun _ => "export-error: input does not decode")
  goalDocumentOf output values file functions negatedLabel groupLabel labels

/-- The premise entries are the premises of the decoded source, in source order. -/
theorem premiseEntries_names (values : List Roles.Bytes.Entry) :
    (GoalRows.premiseEntries values).map (fun entry => entry.original.name) =
      (Roles.premises (Roles.Bytes.source values)).map Roles.Declaration.metadata := by
  simp [GoalRows.premiseEntries, Roles.premises, Roles.Bytes.source, List.filter_map, Function.comp_def]

/-- What a successful goal document is made of. -/
theorem goalDocument_spec {bytes maximumBytes index proof limits maximumPredicates maximumLiterals file functions
    negatedLabel groupLabel labels text}
    (success : goalDocument bytes maximumBytes index proof limits maximumPredicates maximumLiterals file functions
      negatedLabel groupLabel labels = .ok text) :
    ∃ output values names rows negated parents group rowTexts,
      buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output ∧
      Roles.Bytes.decodeBytes bytes maximumBytes = .ok values ∧
      Expanded.attach (expandedOutput output) functions = .ok names ∧
      (GoalRows.goalNames (values.map (fun entry => entry.original.name)) negatedLabel groupLabel labels).Nodup ∧
      GoalRows.Paired (fun entry row => GoalRows.entryRow file entry = .ok row) values rows ∧
      GoalRows.negatedRow negatedLabel output.prepared.goal.metadata output.prepared.goal.original = .ok negated ∧
      (groupParents values negatedLabel).mapM Expanded.parentText = .ok parents ∧
      Expanded.sapRow names output.prepared.replay.problem groupLabel parents = .ok group ∧
      Rows.render names groupLabel labels (Expanded.rows (expandedOutput output)) = .ok rowTexts ∧
      text = String.join (rows.map (· ++ "\n")) ++ negated ++ "\n" ++ group ++ String.join rowTexts ∧
      text.utf8ByteSize ≤ Expanded.maximumDocumentBytes := by
  unfold goalDocument at success
  obtain ⟨output, outputRun, success⟩ := bind_success success
  obtain ⟨values, valuesRun, success⟩ := bind_success success
  unfold goalDocumentOf at success
  obtain ⟨names, namesRun, success⟩ := bind_success success
  split at success
  · rename_i distinct
    obtain ⟨rows, rowsRun, success⟩ := bind_success success
    obtain ⟨negated, negatedRun, success⟩ := bind_success success
    obtain ⟨parents, parentsRun, success⟩ := bind_success success
    obtain ⟨group, groupRun, success⟩ := bind_success success
    obtain ⟨rowTexts, renderRun, success⟩ := bind_success success
    obtain ⟨same, capped⟩ := Expanded.capText_ok success
    subst same
    exact ⟨output, values, names, rows, negated, parents, group, rowTexts, mapError_success outputRun,
      mapError_success valuesRun, namesRun, distinct, GoalRows.mapM_paired rowsRun, negatedRun, parentsRun,
      groupRun, renderRun, rfl, capped⟩
  · cases success

/-- A successful goal document: every decoded declaration is printed with its
    original role, all names of the document are distinct as TPTP names, the
    negated row reads as the negation of the selected conjecture's formula and
    cites that conjecture, the premises entail the conjecture, the last clause
    row is empty, and the text is at most 16 MiB. -/
theorem goalDocument_theorem {bytes maximumBytes index proof limits maximumPredicates maximumLiterals file functions
    negatedLabel groupLabel labels text}
    (success : goalDocument bytes maximumBytes index proof limits maximumPredicates maximumLiterals file functions
      negatedLabel groupLabel labels = .ok text) :
    ∃ output values rows negated,
      buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output ∧
      Roles.Bytes.decodeBytes bytes maximumBytes = .ok values ∧
      GoalRows.Paired (fun (entry : Roles.Bytes.Entry) row =>
        SourceRow.RowReads (GoalRows.roleWord entry.role) file row entry.original.name entry.original.body)
        values rows ∧
      (GoalRows.goalNames (values.map (fun entry => entry.original.name)) negatedLabel groupLabel labels).Nodup ∧
      (∃ entry ∈ values, entry.role = .conjecture ∧ entry.original.name = output.prepared.goal.metadata ∧
        entry.original.body = .fof output.prepared.goal.original) ∧
      GoalRows.NegatedReads negated (.atom negatedLabel) output.prepared.goal.metadata
        (.neg output.prepared.goal.original) ∧
      (∀ (D : Type) (_ : Nonempty D) (model : Fang.Source.Interpretation D),
        Roles.AllHold (Roles.Bytes.sentence (D := D)) (Roles.premises (Roles.Bytes.source values)) model →
          Roles.Bytes.sentence model output.prepared.goal.original) ∧
      ((Expanded.rows (expandedOutput output))[output.certificate.final]?).map Prod.snd = some [] ∧
      text.utf8ByteSize ≤ Expanded.maximumDocumentBytes := by
  obtain ⟨output, values, _, rows, negated, _, _, _, built, decoded, _, distinct, rowsRun, negatedRun, _, _, _,
    _, capped⟩ := goalDocument_spec success
  obtain ⟨other, parsed, _, _, entails⟩ := buildGoal_entails built
  have sameSource := Roles.Bytes.byteParsed_source_unique parsed (Roles.Bytes.decode_grammar decoded)
  rw [sameSource] at entails
  exact ⟨output, values, rows, negated, built, decoded,
    GoalRows.Paired.imp (fun _ _ run => GoalRows.entryRow_reads run) rowsRun, distinct, goal_entry built decoded,
    GoalRows.negatedRow_reads negatedRun, entails, (goal_final_row_empty built).1, capped⟩

/-- The group row of a successful goal document: its parents are the premises of
    the decoded source in order, then the negated goal; its body has exactly one
    reading, a closed formula that holds in a source model exactly when the
    prepared problem holds in the model read through the printed names
    (`Group.groupFormula_spec`); and that reading has SAP for the goal task. -/
theorem goalDocument_group {bytes maximumBytes index proof limits maximumPredicates maximumLiterals file functions
    negatedLabel groupLabel labels text}
    (success : goalDocument bytes maximumBytes index proof limits maximumPredicates maximumLiterals file functions
      negatedLabel groupLabel labels = .ok text) :
    ∃ output values names parents group quoted body formula,
      buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output ∧
      Roles.Bytes.decodeBytes bytes maximumBytes = .ok values ∧
      Expanded.attach (expandedOutput output) functions = .ok names ∧
      groupParents values negatedLabel =
        (Roles.premises (Roles.Bytes.source values)).map Roles.Declaration.metadata ++ [.atom negatedLabel] ∧
      Expanded.sapRow names output.prepared.replay.problem groupLabel parents = .ok group ∧
      group = Expanded.groupRowText quoted body (Expanded.groupAnnotation parents) ∧
      DataText (Expanded.groupAnnotation parents) (Expanded.sapDatum (groupParents values negatedLabel)) ∧
      Group.groupFormula names output.prepared.replay.problem = .ok formula ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      formula.Within [] ∧
      (∀ {D : Type} (model : Fang.Source.Interpretation D),
        (∀ valuation, formula.Holds model valuation) ↔
          Fang.Equality.models (tableModel names.view model) output.prepared.replay.problem) ∧
      (GoalCountermodel bytes maximumBytes output.prepared.goal →
        ∃ (D : Type) (_ : Nonempty D) (model : Fang.Source.Interpretation D),
          ∀ valuation, formula.Holds model valuation) := by
  obtain ⟨output, values, names, _, _, parents, group, _, built, decoded, named, _, _, _, parentsRun, groupRun,
    _, _, _⟩ := goalDocument_spec success
  have printedGroup := groupRun
  unfold Expanded.sapRow at printedGroup
  obtain ⟨quoted, _, printedGroup⟩ := bind_success printedGroup
  obtain ⟨body, bodyRun, printedGroup⟩ := bind_success printedGroup
  obtain ⟨formula, formulaRun, parsed, _, unique, _⟩ := Group.groupText_spec bodyRun
  refine ⟨output, values, names, parents, group, quoted, body, formula, built, decoded, named, ?_, groupRun,
    (Except.ok.inj printedGroup).symm, Expanded.sap_annotation parentsRun, formulaRun, parsed, unique,
    (Group.groupFormula_spec formulaRun).2.1, (Group.groupFormula_spec formulaRun).2.2,
    goal_group_sap built named formulaRun⟩
  rw [groupParents, premiseEntries_names]

/-! The product entry. -/

/-- The negated-goal label, the group label and `count` clause-row labels, all
    starting with one stem that is a prefix of no taken name. -/
def goalLabels (taken : List String) (count : Nat) : String × String × List String :=
  let stem := Expanded.freshPrefix taken "f" "n"
  (stem ++ "0", stem ++ "1", (List.range count).map fun index => stem ++ toString (index + 2))

/-- The atom names of the decoded declarations. -/
def atomNames (values : List Roles.Bytes.Entry) : List String :=
  values.filterMap fun entry =>
    match entry.original.name with
    | .atom value => some value
    | .integer _ => none

def exportGoalLabels (values : List Roles.Bytes.Entry) (output : GoalOutput) : String × String × List String :=
  goalLabels (atomNames values) (Expanded.rows (expandedOutput output)).length

/-- The product entry for goal `index`: the linear lexer and role decoder, the
    original function table with fresh names for the added symbols
    (`Expanded.exportFunctions`), generated labels, then `goalDocumentOf`. -/
def exportGoalDocument (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Aeneas.Std.Usize) (file : String) :
    Except String String :=
  match buildGoalLinear bytes maximumBytes index proof limits maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the goal task is not accepted"
  | .ok output =>
    match Roles.Bytes.decodeBytesLinear bytes maximumBytes with
    | .error _ => .error "export-error: input does not decode"
    | .ok values =>
      goalDocumentOf output values file (Expanded.exportFunctions (expandedOutput output))
        (exportGoalLabels values output).1 (exportGoalLabels values output).2.1 (exportGoalLabels values output).2.2

/-- A product goal document is the `goalDocument` of the generated names, so
    `goalDocument_theorem` and `goalDocument_group` apply to it. -/
theorem exportGoalDocument_spec {bytes maximumBytes index proof limits maximumPredicates maximumLiterals file text}
    (success : exportGoalDocument bytes maximumBytes index proof limits maximumPredicates maximumLiterals file =
      .ok text) :
    ∃ output values,
      buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok output ∧
      Roles.Bytes.decodeBytes bytes maximumBytes = .ok values ∧
      goalDocument bytes maximumBytes index proof limits maximumPredicates maximumLiterals file
        (Expanded.exportFunctions (expandedOutput output)) (exportGoalLabels values output).1
        (exportGoalLabels values output).2.1 (exportGoalLabels values output).2.2 = .ok text := by
  unfold exportGoalDocument at success
  rw [buildGoalLinear_eq, Roles.Bytes.decodeBytesLinear_eq] at success
  cases built : buildGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals with
  | error reason =>
    rw [built] at success
    cases success
  | ok output =>
    rw [built] at success
    cases decoded : Roles.Bytes.decodeBytes bytes maximumBytes with
    | error reason =>
      rw [decoded] at success
      cases success
    | ok values =>
      rw [decoded] at success
      refine ⟨output, values, rfl, rfl, ?_⟩
      unfold goalDocument
      rw [built, decoded]
      exact success

#print axioms Fang.TptpCandidate.GoalDocument.buildGoal_witness
#print axioms Fang.TptpCandidate.GoalDocument.buildGoal_check
#print axioms Fang.TptpCandidate.GoalDocument.buildGoal_accepts
#print axioms Fang.TptpCandidate.GoalDocument.buildGoal_entails
#print axioms Fang.TptpCandidate.GoalDocument.goal_rows
#print axioms Fang.TptpCandidate.GoalDocument.goal_row_checked
#print axioms Fang.TptpCandidate.GoalDocument.goal_final_row_empty
#print axioms Fang.TptpCandidate.GoalDocument.goal_row_local
#print axioms Fang.TptpCandidate.GoalDocument.replayTask_models
#print axioms Fang.TptpCandidate.GoalDocument.prepareGoal_models
#print axioms Fang.TptpCandidate.GoalDocument.goal_group_sap
#print axioms Fang.TptpCandidate.GoalDocument.goal_entry
#print axioms Fang.TptpCandidate.GoalDocument.goal_closed
#print axioms Fang.TptpCandidate.GoalDocument.goalCountermodel_negated
#print axioms Fang.TptpCandidate.GoalDocument.buildGoalLinear_eq
#print axioms Fang.TptpCandidate.GoalDocument.premiseEntries_names
#print axioms Fang.TptpCandidate.GoalDocument.goalDocument_spec
#print axioms Fang.TptpCandidate.GoalDocument.goalDocument_theorem
#print axioms Fang.TptpCandidate.GoalDocument.goalDocument_group
#print axioms Fang.TptpCandidate.GoalDocument.exportGoalDocument_spec

end Fang.TptpCandidate.GoalDocument
