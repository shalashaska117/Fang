/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The named single-file document with the formula height as a parameter: the
   preparation is `prepareNamedD`, decoding at height `maxDepth`; the build, the
   rows, the group and the document are those of `NamedTrace`, `NamedSap` and
   `NamedDocument` over it. At height 64 the export is `exportDocument`. -/
import NamedDocument
import NamedDepthEntry

namespace Fang.TptpCandidate.FullFof.Integration.Named
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-- The replay after decoding keeps the numeric input as the prepared original. -/
theorem replayNamedFrom_original {numeric limits threshold maximumPredicates maximumLiterals prepared}
    (success : replayNamedFrom numeric limits threshold maximumPredicates maximumLiterals = .ok prepared) :
    prepared.original = numeric := by
  unfold replayNamedFrom at success
  obtain ⟨_, _, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  unfold finishNamed at success
  split at success
  next =>
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    obtain ⟨_, _, success⟩ := bind_success success
    cases Except.ok.inj success
    rfl
  next => cases success

theorem prepareNamedD_models {limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals
    prepared}
    (success : prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (satisfiable : CnfBoolean.BytesSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  obtain ⟨numeric, decoded, replay⟩ := bind_success success
  obtain ⟨values, parsed, numericRun⟩ := decodeNumericLimitedD_witness (mapError_success decoded)
  exact replayNamedFrom_models (readInput_below numericRun) replay
    (((decodeUpToD_bytes_satisfiable parsed).trans
      (readInput_satisfiable numericRun (decodeUpToD_closed parsed))).mp satisfiable)

theorem prepareNamedD_original {limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals
    prepared}
    (success : prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared) :
    ∃ values, decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok values ∧
      readInput values = some prepared.original := by
  obtain ⟨numeric, decoded, replay⟩ := bind_success success
  rw [replayNamedFrom_original replay]
  exact decodeNumericLimitedD_witness (mapError_success decoded)

/-- At height 64 the preparation is `prepareNamed`. -/
theorem prepareNamedD_accepted (limit : Nat) : prepareNamedD limit 64 = prepareNamed limit := by
  have decoded : decodeNumericLimitedD limit 64 = decodeNumericLimited limit := by
    funext bytes maximumBytes
    unfold decodeNumericLimitedD decodeNumericLimited
    rw [decodeBytesLimitedD_eq, decodeBytesLimited_eq, decodeBytesUpToD_accepted]
    rfl
  funext bytes maximumBytes limits threshold maximumPredicates maximumLiterals
  unfold prepareNamedD
  rw [decoded, prepareNamed_eq]

end Fang.TptpCandidate.FullFof.Integration.Named

namespace Fang.QuantifiedEqualityTstp.NamedExport
open Fang.TptpCandidate Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration TstpText
open Expanded (Output WellFormed legacyPrepared originals parentText parentDatum sapRow capText capText_ok
  maximumDocumentBytes documentNames groupRowText groupAnnotation sapDatum sap_annotation)

private theorem bind_ok {α β : Type} {action : Except String α}
    {next : α → Except String β} {result : β}
    (success : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error reason => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem group_sapD {limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals prepared}
    (success : Named.prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    {originalFunctions originalPredicates : List (String × Nat)} {names : Body.Names}
    (checked : Checked originalFunctions originalPredicates
      ⟨prepared.problem, prepared.functionArities, prepared.predicateArities⟩ names)
    (wellFormed : prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed
      prepared.functionArities prepared.predicateArities) = true)
    {formula : NamedQuantifiedEquality.Formula}
    (formulaRun : Group.groupFormula names prepared.problem = .ok formula)
    (satisfiable : CnfBoolean.BytesSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨D, nonempty, model, holds⟩ := Named.prepareNamedD_models success satisfiable
  exact ⟨D, nonempty, Expanded.namedModel names model,
    group_models checked wellFormed formulaRun model holds⟩

/-- The same replay, envelope decoder, signature gate and ordered step checker
    as `accepts`, with the checked clauses retained. No rule is reimplemented. -/
def buildD (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) : Except BuildError Expanded.Output :=
  match Named.prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals with
  | .error reason => .error (.replay reason)
  | .ok prepared =>
    match decodeV8 proof with
    | .error reason => .error (.certificate reason)
    | .ok certificate =>
      if WellFormed prepared certificate then
        match retain prepared.problem certificate with
        | .error reason => .error (.inference reason)
        | .ok clauses => .ok ⟨prepared, certificate, clauses⟩
      else .error .signature

theorem buildD_witness {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Named.prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals = .ok output.prepared ∧
      decodeV8 proof = .ok output.certificate ∧ WellFormed output.prepared output.certificate = true ∧
      retain output.prepared.problem output.certificate = .ok output.clauses := by
  cases preparedRun : Named.prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates maximumLiterals with
  | error reason => simp [buildD, preparedRun] at success
  | ok prepared =>
    cases decoded : decodeV8 proof with
    | error reason => simp [buildD, preparedRun, decoded] at success
    | ok certificate =>
      by_cases valid : WellFormed prepared certificate = true
      · cases retained : retain prepared.problem certificate with
        | error reason => simp [buildD, preparedRun, decoded, valid, retained] at success
        | ok clauses =>
          simp [buildD, preparedRun, decoded, valid, retained] at success
          subst success
          exact ⟨rfl, rfl, valid, retained⟩
      · simp [buildD, preparedRun, decoded, valid] at success

theorem buildD_check {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Fang.Equality.Ordered.check output.prepared.problem output.certificate = .ok () := by
  rw [← retain_erases, (buildD_witness success).2.2.2]
  rfl

theorem buildD_original_unsat {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes :=
  Named.prepareNamedD_check_original_unsat (buildD_witness success).1 output.certificate (buildD_check success)

/-- A successful build is exactly an accepted version-8 pair. -/
theorem buildD_accepts {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Named.acceptsNamedD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok () := by
  obtain ⟨preparedRun, decoded, wellFormed, _⟩ := buildD_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  simp [Named.acceptsNamedD, checkProblem, preparedRun, decoded, wellFormed, buildD_check success,
    Except.mapError, bind, Except.bind]

theorem buildD_rows {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    Derivation.Checked output.prepared.problem [] (rows output) ∧
      (rows output).map Prod.snd = output.clauses := by
  obtain ⟨checkedSteps, _, _, _⟩ := retain_witness (buildD_witness success).2.2.2
  obtain ⟨values, checked, sameSteps, sameClauses⟩ := Derivation.checkSteps_rows checkedSteps
  simp only [List.nil_append] at sameClauses
  have paired : rows output = values := by
    rw [rows, ← sameSteps, ← sameClauses, Derivation.zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameClauses⟩

theorem buildD_row_checked {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : rows output = leading ++ value :: rest) :
    Fang.Equality.Ordered.checkStep output.prepared.problem (leading.map Prod.snd) value.1 = .ok value.2 := by
  have checked := (buildD_rows success).1
  rw [position] at checked
  simpa using checked.row

/-- SAP for the group of a built pair under attached names. -/
theorem buildD_group_sap {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output)
    {proposed names} (named : attach output proposed = .ok names)
    {formula} (formulaRun : Group.groupFormula names output.prepared.problem = .ok formula)
    (satisfiable : CnfBoolean.BytesSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨preparedRun, _, wellFormed, _⟩ := buildD_witness success
  simp only [WellFormed, Bool.and_eq_true] at wellFormed
  exact group_sapD preparedRun (attach_spec named) wellFormed.1 formulaRun satisfiable

def documentD (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) (functions : Body.Names)
    (file groupLabel : String) (labels : List String) : Except String String :=
  match buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these bytes"
  | .ok output => documentOf output functions file groupLabel labels

/-- The source rows restate exactly the declarations decoded from the original bytes. -/
theorem originalsD_decoded {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (built : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok (originals output) := by
  obtain ⟨values, decoded, numericRun⟩ := Named.prepareNamedD_original (buildD_witness built).1
  rw [originals, readInput_originals numericRun]
  exact decoded

structure DocumentFactsD (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize)
    (functions : Body.Names) (file groupLabel : String) (labels : List String)
    (text : String) : Prop where
  facts : ∃ output names sources parents group rowTexts,
    buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
    Named.acceptsNamedD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok () ∧
    decodeBytesUpToD limit maxDepth bytes maximumBytes = .ok (originals output) ∧
    attach output functions = .ok names ∧
    SourceRow.RowsRead "axiom" file (originals output) sources ∧
    ((originals output).map Declaration.name).mapM parentText = .ok parents ∧
    sapRow names output.prepared.problem groupLabel parents = .ok group ∧
    Rows.render names groupLabel labels (rows output) = .ok rowTexts ∧
    (documentNames ((originals output).map Declaration.name) groupLabel labels).Nodup ∧
    text = String.join (sources.map fun row => row.2 ++ "\n") ++ group ++ String.join rowTexts ∧
    text.utf8ByteSize ≤ maximumDocumentBytes

theorem documentD_spec {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
    groupLabel labels text}
    (success : documentD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    DocumentFactsD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
      groupLabel labels text := by
  cases built : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | error reason => simp [documentD, built] at success
  | ok output =>
    by_cases distinct : (documentNames ((originals output).map Declaration.name) groupLabel labels).Nodup
    · simp only [documentD, documentOf, built, distinct, decide_true] at success
      unfold assemble at success
      obtain ⟨names, namesRun, success⟩ := bind_ok success
      obtain ⟨sources, sourcesRun, success⟩ := bind_ok success
      obtain ⟨parents, parentsRun, success⟩ := bind_ok success
      obtain ⟨group, groupRun, success⟩ := bind_ok success
      obtain ⟨rowTexts, rowsRun, success⟩ := bind_ok success
      obtain ⟨same, capped⟩ := capText_ok success
      subst same
      exact ⟨⟨output, names, sources, parents, group, rowTexts, built, buildD_accepts built,
        originalsD_decoded built, namesRun, SourceRow.sourceRows_spec sourcesRun, parentsRun, groupRun,
        rowsRun, distinct, rfl, capped⟩⟩
    · simp [documentD, documentOf, built, distinct] at success

/-- A printed document certifies the original bytes unsatisfiable. -/
theorem documentD_original_unsat {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals
    functions file groupLabel labels text}
    (success : documentD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨⟨output, _, _, _, _, _, built, _⟩⟩ := documentD_spec success
  exact buildD_original_unsat built

/-- SAP for the group row of a printed document: the row is printed from the
    attached names and the prepared problem of an accepted pair, it has one
    reading, and if the original bytes have a model then that reading holds in
    some source model. -/
theorem documentD_group_sap {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
    groupLabel labels text}
    (success : documentD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    ∃ output names parents group quoted body formula,
      buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      attach output functions = .ok names ∧
      ((originals output).map Declaration.name).mapM parentText = .ok parents ∧
      sapRow names output.prepared.problem groupLabel parents = .ok group ∧
      group = groupRowText quoted body (groupAnnotation parents) ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      (CnfBoolean.BytesSatisfiable bytes maximumBytes →
        ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          ∀ valuation, formula.Holds model valuation) := by
  obtain ⟨⟨output, names, _, parents, group, _, built, _, _, namesRun, _, parentsRun, groupRun, _⟩⟩ :=
    documentD_spec success
  obtain ⟨quoted, body, formula, printed, _, formulaRun, parsed, _, unique, _⟩ :=
    document_group parentsRun groupRun
  exact ⟨output, names, parents, group, quoted, body, formula, built, namesRun, parentsRun, groupRun,
    printed, parsed, unique, fun satisfiable => buildD_group_sap built namesRun formulaRun satisfiable⟩

/-- Each printed clause row follows from its parent rows; an input row from the
    prepared problem, which the group row states. -/
theorem rowD_local {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (built : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output)
    {leading : List Derivation.Row} {value : Derivation.Row} {rest : List Derivation.Row}
    (position : rows output = leading ++ value :: rest)
    {names : Body.Names} {named : List EqualitySource.Literal} (same : Body.NamedClause names value.2 named)
    {D : Type} (model : Source.Interpretation D) (label : String)
    (parentsPrinted : ∀ parent ∈ value.1.parents, ∀ row, leading[parent]? = some row →
      ∃ parentNamed, Body.NamedClause names row.2 parentNamed)
    (parents : ∀ parent ∈ value.1.parents, ∀ row, leading[parent]? = some row →
      ∀ parentNamed, Body.NamedClause names row.2 parentNamed →
        (EqualitySource.Clause.mk "" parentNamed).Valid model)
    (group : ∀ index, value.1 = .input index →
      Fang.Equality.models (tableModel names.view model) output.prepared.problem) :
    (EqualitySource.Clause.mk label named).Valid model := by
  rw [Group.namedClause_valid_iff same model label]
  apply Local.step_local (buildD_row_checked built position) (tableModel names.view model)
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

/-- The last retained row is the empty clause. -/
theorem finalD_row_empty {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (built : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ((rows output)[output.certificate.final]?).map Prod.snd = some [] ∧
      output.certificate.final + 1 = (rows output).length := by
  obtain ⟨checkedSteps, stepsLength, last, empty⟩ := retain_witness (buildD_witness built).2.2.2
  have clauses := (buildD_rows built).2
  have clausesLength := congrArg List.length clauses
  simp only [List.length_map] at clausesLength
  refine ⟨?_, by rw [clausesLength]; exact last⟩
  rw [← clauses] at empty
  simpa using empty

def exportDocumentD (limit maxDepth : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize)
    (file : String) : Except String String :=
  match buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these bytes"
  | .ok output => documentOf output (outputNames output) file
      (Expanded.exportLabels output).1 (Expanded.exportLabels output).2

theorem exportDocumentD_spec {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file text}
    (success : exportDocumentD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file =
      .ok text) :
    ∃ output, buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      DocumentFactsD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals
        (outputNames output) file (Expanded.exportLabels output).1 (Expanded.exportLabels output).2 text := by
  unfold exportDocumentD at success
  cases built : buildD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | error reason => rw [built] at success; cases success
  | ok output =>
    rw [built] at success
    refine ⟨output, rfl, documentD_spec ?_⟩
    unfold documentD
    rw [built]
    exact success

theorem exportDocumentD_original_unsat {limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals
    file text}
    (success : exportDocumentD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file =
      .ok text) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨output, built, _⟩ := exportDocumentD_spec success
  exact buildD_original_unsat built

/-- At height 64 the export is `exportDocument`. -/
theorem exportDocumentD_accepted (limit : Nat) : exportDocumentD limit 64 = exportDocument limit := by
  funext bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file
  unfold exportDocumentD exportDocument buildD build
  rw [Named.prepareNamedD_accepted]
  rfl

end Fang.QuantifiedEqualityTstp.NamedExport
