/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Named signed inputs-task documents. The input is one signed file with no
   conjecture, and its inputs, premises and negated conjectures alike, are
   refuted. Every declaration is printed with its original role, then the SAP
   group whose parents are every premise and negated-conjecture entry in source
   order, then the clause rows. This is the goal document without the negated
   goal row. -/
import NamedGoalDocumentDepth

namespace Fang.TptpCandidate.Roles.Signed.DepthNamed
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

theorem prepareInputsNamed_witness {limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals
    prepared}
    (success : prepareInputsNamed limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared) :
    ∃ values input,
      Bytes.decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok values ∧ readSigned values = some input ∧
      Roles.goals (Bytes.source values) = [] ∧
      replayNamedTask input (inputsTask input) limits threshold maximumPredicates maximumLiterals = .ok prepared := by
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
    exact ⟨values, input, decoded, read, noGoals, success⟩
  · cases success

/-- The model direction of the inputs task: a model of the inputs gives a model
    of the prepared problem. -/
theorem prepareInputsNamed_models {limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals
    prepared}
    (success : prepareInputsNamed limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (satisfiable : Bytes.BytesInputsSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  obtain ⟨values, input, decoded, read, noGoals, replayRun⟩ := prepareInputsNamed_witness success
  have closed := Bytes.decodeUpToD_closed decoded
  rw [Bytes.parsed_inputs_satisfiable (Bytes.decodeUpToD_grammar decoded) closed noGoals] at satisfiable
  obtain ⟨D, inhabited, model, holds⟩ := satisfiable
  exact replayNamedTask_models_below (retained_below read (inputsTask_fromRows input)) replayRun
    ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates,
      (inputsTask_models read closed (model_toNumeric model _ _)).mpr holds⟩

end Fang.TptpCandidate.Roles.Signed.DepthNamed

namespace Fang.TptpCandidate.InputsDocument.NamedDepth
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.Roles.Numeric Fang.TptpCandidate.Roles.Signed
open Fang.TptpCandidate.Roles.Signed.DepthNamed
open Fang.TptpCandidate.GoalDocument.NamedDepth (GoalBuildError GoalWellFormed)
open Fang.QuantifiedEqualityTstp Fang.TstpText
open FangQuantifiedEqualityReplay (bind_success mapError_success)

structure InputsOutput where
  replay : Roles.Signed.SignedPrepared
  certificate : Fang.Equality.Ordered.Certificate
  clauses : List Fang.Equality.Clause

/-- The signed prepare for the inputs task, then the envelope decoder, signature
    gate and ordered step checker of `DepthNamed.acceptsInputsNamed`, keeping the checked clauses. -/
def buildInputs (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) :
    Except GoalBuildError InputsOutput :=
  match DepthNamed.prepareInputsNamed limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals with
  | .error reason => .error (.replay reason)
  | .ok replay =>
    match Integration.decodeV8 proof with
    | .error reason => .error (.certificate reason)
    | .ok certificate =>
      if GoalWellFormed replay certificate then
        match retain replay.problem certificate with
        | .error reason => .error (.inference reason)
        | .ok clauses => .ok ⟨replay, certificate, clauses⟩
      else .error .signature

theorem buildInputs_witness {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    DepthNamed.prepareInputsNamed limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals = .ok output.replay ∧
      Integration.decodeV8 proof = .ok output.certificate ∧
      GoalWellFormed output.replay output.certificate = true ∧
      retain output.replay.problem output.certificate = .ok output.clauses := by
  cases preparedRun : DepthNamed.prepareInputsNamed limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals with
  | error reason => simp [buildInputs, preparedRun] at success
  | ok replay =>
    cases decoded : Integration.decodeV8 proof with
    | error reason => simp [buildInputs, preparedRun, decoded] at success
    | ok certificate =>
      by_cases valid : GoalWellFormed replay certificate = true
      · cases retained : retain replay.problem certificate with
        | error reason => simp [buildInputs, preparedRun, decoded, valid, retained] at success
        | ok clauses =>
          simp [buildInputs, preparedRun, decoded, valid, retained] at success
          subst success
          exact ⟨rfl, rfl, valid, retained⟩
      · simp [buildInputs, preparedRun, decoded, valid] at success

theorem buildInputs_check {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Fang.Equality.Ordered.check output.replay.problem output.certificate = .ok () := by
  rw [← retain_erases, (buildInputs_witness success).2.2.2]
  rfl

/-- A successful inputs build is an accepted `DepthNamed.acceptsInputsNamed` pair. Only this direction is proved. -/
theorem buildInputs_accepts {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    DepthNamed.acceptsInputsNamed limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok () := by
  obtain ⟨preparedRun, decoded, wellFormed, _⟩ := buildInputs_witness success
  simp only [GoalWellFormed, Bool.and_eq_true] at wellFormed
  simp [DepthNamed.acceptsInputsNamed, Integration.checkProblem, preparedRun, decoded, wellFormed, buildInputs_check success,
    Except.mapError, bind, Except.bind]

/-- Refutation endpoint: the inputs of the file are not satisfiable. -/
theorem buildInputs_unsat {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ¬ Roles.Bytes.BytesInputsSatisfiable bytes maximumBytes :=
  DepthNamed.acceptsInputsNamed_unsat (buildInputs_accepts success)

/-! Clause rows, as for the goal task. -/

def expandedOutput (output : InputsOutput) : Expanded.Output :=
  ⟨⟨Roles.Signed.tables output.replay.input, output.replay.problem,
    output.replay.functionArities, output.replay.predicateArities⟩,
    output.certificate, output.clauses⟩

theorem inputs_rows {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Derivation.Checked output.replay.problem [] (Expanded.rows (expandedOutput output)) ∧
      (Expanded.rows (expandedOutput output)).map Prod.snd = output.clauses := by
  obtain ⟨checkedSteps, _, _, _⟩ := retain_witness (buildInputs_witness success).2.2.2
  obtain ⟨values, checked, sameSteps, sameClauses⟩ := Derivation.checkSteps_rows checkedSteps
  simp only [List.nil_append] at sameClauses
  have paired : Expanded.rows (expandedOutput output) = values := by
    show output.certificate.steps.zip output.clauses = values
    rw [← sameSteps, ← sameClauses, Derivation.zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameClauses⟩

theorem inputs_row_checked {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : Expanded.rows (expandedOutput output) = leading ++ value :: rest) :
    Fang.Equality.Ordered.checkStep output.replay.problem (leading.map Prod.snd) value.1 = .ok value.2 := by
  have checked := (inputs_rows success).1
  rw [position] at checked
  simpa using checked.row

/-- The last retained row is the empty clause. -/
theorem inputs_final_row_empty {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (built : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ((Expanded.rows (expandedOutput output))[output.certificate.final]?).map Prod.snd = some [] ∧
      output.certificate.final + 1 = (Expanded.rows (expandedOutput output)).length := by
  obtain ⟨_, _, last, empty⟩ := retain_witness (buildInputs_witness built).2.2.2
  have clauses := (inputs_rows built).2
  have clausesLength := congrArg List.length clauses
  simp only [List.length_map] at clausesLength
  refine ⟨?_, by rw [clausesLength]; exact last⟩
  rw [← clauses] at empty
  simpa using empty

/-- Each printed clause row follows from its parent rows; an input row from the
    prepared problem, which the group row states. -/
theorem inputs_row_local {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (built : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output)
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
      Fang.Equality.models (tableModel names.view model) output.replay.problem) :
    (EqualitySource.Clause.mk label named).Valid model := by
  rw [Group.namedClause_valid_iff same model label]
  apply Local.step_local (inputs_row_checked built position) (tableModel names.view model)
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

/-- SAP for the inputs task: if the inputs of the file have a model, the
    printed group formula holds in some source model. -/
theorem inputs_group_sap {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (built : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output)
    {functions names} (named : NamedExport.attach (expandedOutput output) functions = .ok names)
    {formula} (formulaRun : Group.groupFormula names output.replay.problem = .ok formula)
    (satisfiable : Roles.Bytes.BytesInputsSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨preparedRun, _, wellFormed, _⟩ := buildInputs_witness built
  simp only [GoalWellFormed, Bool.and_eq_true] at wellFormed
  obtain ⟨D, nonempty, model, holds⟩ := DepthNamed.prepareInputsNamed_models preparedRun satisfiable
  have namedHolds := NamedExport.namedModel_models (prepared := ⟨output.replay.problem,
    output.replay.functionArities, output.replay.predicateArities⟩)
    (NamedExport.attach_spec named) wellFormed.1 model holds
  exact ⟨D, nonempty, Expanded.namedModel names model,
    ((Group.groupFormula_spec formulaRun).2.2 (Expanded.namedModel names model)).mpr namedHolds⟩

/-! The document. -/

/-- The entries an inputs task keeps, by the role policy of `Roles.positiveInputs`:
    the premises and the negated conjectures. -/
def inputEntries (values : List Roles.Bytes.Entry) : List Roles.Bytes.Entry :=
  values.filter (fun entry => decide (Roles.classify entry.role = .ok .premise ∨
    Roles.classify entry.role = .ok .alreadyNegated))

/-- The parents of the group row: every premise and negated-conjecture entry, in source order. -/
def groupParents (values : List Roles.Bytes.Entry) : List Fang.TptpCandidate.Name :=
  (inputEntries values).map (fun entry => entry.original.name)

/-- Every name of an inputs document, compared as TPTP names: each declaration,
    the group, then one per clause row. -/
def inputsNames (sources : List Fang.TptpCandidate.Name) (groupLabel : String) (labels : List String) :
    List Fang.TptpCandidate.Name :=
  sources ++ .atom groupLabel :: labels.map Fang.TptpCandidate.Name.atom

/-- The document text of a built inputs task and its decoded declarations. -/
def inputsDocumentOf (output : InputsOutput) (values : List Roles.Bytes.Entry) (file : String)
    (functions : Body.Names) (groupLabel : String) (labels : List String) : Except String String := do
  let names ← NamedExport.attach (expandedOutput output) functions
  if (inputsNames (values.map (fun entry => entry.original.name)) groupLabel labels).Nodup then
    let rows ← values.mapM (GoalRows.entryRow file)
    let parents ← (groupParents values).mapM Expanded.parentText
    let group ← Expanded.sapRow names output.replay.problem groupLabel parents
    let rowTexts ← Rows.render names groupLabel labels (Expanded.rows (expandedOutput output))
    Expanded.capText (String.join (rows.map (· ++ "\n")) ++ group ++ String.join rowTexts)
  else .error "export-error: document names are not distinct"

def inputsDocument (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) (file : String)
    (functions : Body.Names) (groupLabel : String) (labels : List String) : Except String String := do
  let output ← (buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals).mapError
    (fun _ => "export-error: the inputs task is not accepted")
  let values ← (Roles.Bytes.decodeBytesUpToD limit maxDepth bytes maximumBytes).mapError (fun _ => "export-error: input does not decode")
  inputsDocumentOf output values file functions groupLabel labels

/-- The group parents are the positive inputs of the decoded source, in source order. -/
theorem groupParents_names (values : List Roles.Bytes.Entry) :
    groupParents values = (Roles.positiveInputs (Roles.Bytes.source values)).map Roles.Declaration.metadata := by
  simp [groupParents, inputEntries, Roles.positiveInputs, Roles.Bytes.source, List.filter_map, Function.comp_def]

/-- What a successful inputs document is made of. -/
theorem inputsDocument_spec {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file functions
    groupLabel labels text}
    (success : inputsDocument limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file functions
      groupLabel labels = .ok text) :
    ∃ output values names rows parents group rowTexts,
      buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      Roles.Bytes.decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok values ∧
      NamedExport.attach (expandedOutput output) functions = .ok names ∧
      (inputsNames (values.map (fun entry => entry.original.name)) groupLabel labels).Nodup ∧
      GoalRows.Paired (fun entry row => GoalRows.entryRow file entry = .ok row) values rows ∧
      (groupParents values).mapM Expanded.parentText = .ok parents ∧
      Expanded.sapRow names output.replay.problem groupLabel parents = .ok group ∧
      Rows.render names groupLabel labels (Expanded.rows (expandedOutput output)) = .ok rowTexts ∧
      text = String.join (rows.map (· ++ "\n")) ++ group ++ String.join rowTexts ∧
      text.utf8ByteSize ≤ Expanded.maximumDocumentBytes := by
  unfold inputsDocument at success
  obtain ⟨output, outputRun, success⟩ := bind_success success
  obtain ⟨values, valuesRun, success⟩ := bind_success success
  unfold inputsDocumentOf at success
  obtain ⟨names, namesRun, success⟩ := bind_success success
  split at success
  · rename_i distinct
    obtain ⟨rows, rowsRun, success⟩ := bind_success success
    obtain ⟨parents, parentsRun, success⟩ := bind_success success
    obtain ⟨group, groupRun, success⟩ := bind_success success
    obtain ⟨rowTexts, renderRun, success⟩ := bind_success success
    obtain ⟨same, capped⟩ := Expanded.capText_ok success
    subst same
    exact ⟨output, values, names, rows, parents, group, rowTexts, mapError_success outputRun,
      mapError_success valuesRun, namesRun, distinct, GoalRows.mapM_paired rowsRun, parentsRun,
      groupRun, renderRun, rfl, capped⟩
  · cases success

/-- A successful inputs document: every decoded declaration is printed with its
    original role, all names of the document are distinct as TPTP names, the
    file has no conjecture, its inputs are not satisfiable, the last clause row
    is empty, and the text is at most 16 MiB. -/
theorem inputsDocument_theorem {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file
    functions groupLabel labels text}
    (success : inputsDocument limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file functions
      groupLabel labels = .ok text) :
    ∃ output values rows,
      buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      Roles.Bytes.decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok values ∧
      GoalRows.Paired (fun (entry : Roles.Bytes.Entry) row =>
        SourceRow.RowReads (GoalRows.roleWord entry.role) file row entry.original.name entry.original.body)
        values rows ∧
      (inputsNames (values.map (fun entry => entry.original.name)) groupLabel labels).Nodup ∧
      Roles.goals (Roles.Bytes.source values) = [] ∧
      ¬ Roles.Bytes.BytesInputsSatisfiable bytes maximumBytes ∧
      ((Expanded.rows (expandedOutput output))[output.certificate.final]?).map Prod.snd = some [] ∧
      text.utf8ByteSize ≤ Expanded.maximumDocumentBytes := by
  obtain ⟨output, values, _, rows, _, _, _, built, decoded, _, distinct, rowsRun, _, _, _, _, capped⟩ :=
    inputsDocument_spec success
  obtain ⟨otherValues, _, otherDecoded, _, noGoals, _⟩ :=
    DepthNamed.prepareInputsNamed_witness (buildInputs_witness built).1
  have sameValues : otherValues = values := Except.ok.inj (otherDecoded.symm.trans decoded)
  subst sameValues
  exact ⟨output, otherValues, rows, built, decoded,
    GoalRows.Paired.imp (fun _ _ run => GoalRows.entryRow_reads run) rowsRun, distinct, noGoals,
    buildInputs_unsat built, (inputs_final_row_empty built).1, capped⟩

/-- The group row of a successful inputs document: its parents are the premises
    and negated conjectures of the decoded source in order; its body has exactly
    one reading, a closed formula that holds in a source model exactly when the
    prepared problem holds in the model read through the printed names
    (`Group.groupFormula_spec`); and that reading has SAP for the inputs task. -/
theorem inputsDocument_group {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file
    functions groupLabel labels text}
    (success : inputsDocument limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file functions
      groupLabel labels = .ok text) :
    ∃ output values names parents group quoted body formula,
      buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      Roles.Bytes.decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok values ∧
      NamedExport.attach (expandedOutput output) functions = .ok names ∧
      groupParents values = (Roles.positiveInputs (Roles.Bytes.source values)).map Roles.Declaration.metadata ∧
      Expanded.sapRow names output.replay.problem groupLabel parents = .ok group ∧
      group = Expanded.groupRowText quoted body (Expanded.groupAnnotation parents) ∧
      DataText (Expanded.groupAnnotation parents) (Expanded.sapDatum (groupParents values)) ∧
      Group.groupFormula names output.replay.problem = .ok formula ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      formula.Within [] ∧
      (∀ {D : Type} (model : Fang.Source.Interpretation D),
        (∀ valuation, formula.Holds model valuation) ↔
          Fang.Equality.models (tableModel names.view model) output.replay.problem) ∧
      (Roles.Bytes.BytesInputsSatisfiable bytes maximumBytes →
        ∃ (D : Type) (_ : Nonempty D) (model : Fang.Source.Interpretation D),
          ∀ valuation, formula.Holds model valuation) := by
  obtain ⟨output, values, names, _, parents, group, _, built, decoded, named, _, _, parentsRun, groupRun,
    _, _, _⟩ := inputsDocument_spec success
  have printedGroup := groupRun
  unfold Expanded.sapRow at printedGroup
  obtain ⟨quoted, _, printedGroup⟩ := bind_success printedGroup
  obtain ⟨body, bodyRun, printedGroup⟩ := bind_success printedGroup
  obtain ⟨formula, formulaRun, parsed, _, unique, _⟩ := Group.groupText_spec bodyRun
  exact ⟨output, values, names, parents, group, quoted, body, formula, built, decoded, named, groupParents_names values,
    groupRun, (Except.ok.inj printedGroup).symm, Expanded.sap_annotation parentsRun, formulaRun, parsed, unique,
    (Group.groupFormula_spec formulaRun).2.1, (Group.groupFormula_spec formulaRun).2.2,
    inputs_group_sap built named formulaRun⟩

/-! The product entry. -/

/-- The group label and `count` clause-row labels, all starting with one stem
    that is a prefix of no taken name. -/
def inputsLabels (taken : List String) (count : Nat) : String × List String :=
  let stem := Expanded.freshPrefix taken "f" "n"
  (stem ++ "0", (List.range count).map fun index => stem ++ toString (index + 1))

def exportInputsLabels (values : List Roles.Bytes.Entry) (output : InputsOutput) : String × List String :=
  inputsLabels (GoalDocument.NamedDepth.atomNames values) (Expanded.rows (expandedOutput output)).length

/-- The product entry for the inputs task: the linear lexer and role decoder,
    the original function table with fresh names for the added symbols
    (`NamedExport.outputNames`), generated labels, then `inputsDocumentOf`. -/
def exportInputsDocument (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) (file : String) :
    Except String String :=
  match buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the inputs task is not accepted"
  | .ok output =>
    match Roles.Bytes.decodeBytesLimitedD limit maxDepth bytes maximumBytes with
    | .error _ => .error "export-error: input does not decode"
    | .ok values =>
      inputsDocumentOf output values file (NamedExport.outputNames (expandedOutput output))
        (exportInputsLabels values output).1 (exportInputsLabels values output).2

/-- A product inputs document is the `inputsDocument` of the generated names, so
    `inputsDocument_theorem` and `inputsDocument_group` apply to it. -/
theorem exportInputsDocument_spec {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file
    text}
    (success : exportInputsDocument limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file =
      .ok text) :
    ∃ output values,
      buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      Roles.Bytes.decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok values ∧
      inputsDocument limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file
        (NamedExport.outputNames (expandedOutput output)) (exportInputsLabels values output).1
        (exportInputsLabels values output).2 = .ok text := by
  unfold exportInputsDocument at success
  rw [Roles.Bytes.decodeBytesLimitedD_eq] at success
  cases built : buildInputs limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | error reason =>
    rw [built] at success
    cases success
  | ok output =>
    rw [built] at success
    cases decoded : Roles.Bytes.decodeBytesUpToD limit maxDepth bytes maximumBytes with
    | error reason =>
      rw [decoded] at success
      cases success
    | ok values =>
      rw [decoded] at success
      refine ⟨output, values, rfl, rfl, ?_⟩
      unfold inputsDocument
      rw [built, decoded]
      exact success

#print axioms Fang.TptpCandidate.Roles.Signed.DepthNamed.prepareInputsNamed_models
#print axioms Fang.TptpCandidate.InputsDocument.NamedDepth.buildInputs_unsat
#print axioms Fang.TptpCandidate.InputsDocument.NamedDepth.inputs_row_local
#print axioms Fang.TptpCandidate.InputsDocument.NamedDepth.inputs_group_sap
#print axioms Fang.TptpCandidate.InputsDocument.NamedDepth.inputsDocument_theorem
#print axioms Fang.TptpCandidate.InputsDocument.NamedDepth.inputsDocument_group
#print axioms Fang.TptpCandidate.InputsDocument.NamedDepth.exportInputsDocument_spec

end Fang.TptpCandidate.InputsDocument.NamedDepth
