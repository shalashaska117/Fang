/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Full TSTP document over named preparation and checked predicate names. -/
import NamedTrace

namespace Fang.QuantifiedEqualityTstp.NamedExport
open Fang.TptpCandidate Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration TstpText
open Expanded (originals parentText parentDatum sapRow capText capText_ok maximumDocumentBytes
  documentNames groupRowText groupAnnotation sapDatum sap_annotation)

/-- Body of the document after a successful build. -/
def assemble (output : Expanded.Output) (functions : Body.Names) (file groupLabel : String)
    (labels : List String) : Except String String := do
  let names ← attach output functions
  let sources ← SourceRow.sourceRows (originals output) file
  let parents ← ((originals output).map Declaration.name).mapM parentText
  let group ← sapRow names output.prepared.problem groupLabel parents
  let rowTexts ← Rows.render names groupLabel labels (rows output)
  capText (String.join (sources.map fun row => row.2 ++ "\n") ++ group ++ String.join rowTexts)

def documentOf (output : Expanded.Output) (functions : Body.Names) (file groupLabel : String)
    (labels : List String) : Except String String :=
  if decide (documentNames ((originals output).map Declaration.name) groupLabel labels).Nodup then
    assemble output functions file groupLabel labels
  else .error "export-error: document names are not distinct"

def document (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String) (limits : FangOriginalReplay.Limits)
    (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize) (functions : Body.Names)
    (file groupLabel : String) (labels : List String) : Except String String :=
  match build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these bytes"
  | .ok output => documentOf output functions file groupLabel labels

private theorem bind_ok {α β : Type} {action : Except String α}
    {next : α → Except String β} {result : β}
    (success : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error reason => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem readInput_originals {values : List Declaration} {input : NumericInput}
    (success : readInput values = some input) : input.rows.map NumericRow.original = values :=
  (readInput_tables success).2.2

/-- The source rows restate exactly the declarations decoded from the original bytes. -/
theorem originals_decoded {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (built : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    decodeBytesUpTo limit bytes maximumBytes = .ok (originals output) := by
  obtain ⟨values, decoded, numericRun⟩ := Named.prepareNamed_original (build_witness built).1
  rw [originals, readInput_originals numericRun]
  exact decoded

structure DocumentFacts (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize)
    (functions : Body.Names) (file groupLabel : String) (labels : List String)
    (text : String) : Prop where
  facts : ∃ output names sources parents group rowTexts,
    build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
    Named.acceptsNamed limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok () ∧
    decodeBytesUpTo limit bytes maximumBytes = .ok (originals output) ∧
    attach output functions = .ok names ∧
    SourceRow.RowsRead "axiom" file (originals output) sources ∧
    ((originals output).map Declaration.name).mapM parentText = .ok parents ∧
    sapRow names output.prepared.problem groupLabel parents = .ok group ∧
    Rows.render names groupLabel labels (rows output) = .ok rowTexts ∧
    (documentNames ((originals output).map Declaration.name) groupLabel labels).Nodup ∧
    text = String.join (sources.map fun row => row.2 ++ "\n") ++ group ++ String.join rowTexts ∧
    text.utf8ByteSize ≤ maximumDocumentBytes

theorem document_spec {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
    groupLabel labels text}
    (success : document limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    DocumentFacts limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
      groupLabel labels text := by
  cases built : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | error reason => simp [document, built] at success
  | ok output =>
    by_cases distinct : (documentNames ((originals output).map Declaration.name) groupLabel labels).Nodup
    · simp only [document, documentOf, built, distinct, decide_true] at success
      unfold assemble at success
      obtain ⟨names, namesRun, success⟩ := bind_ok success
      obtain ⟨sources, sourcesRun, success⟩ := bind_ok success
      obtain ⟨parents, parentsRun, success⟩ := bind_ok success
      obtain ⟨group, groupRun, success⟩ := bind_ok success
      obtain ⟨rowTexts, rowsRun, success⟩ := bind_ok success
      obtain ⟨same, capped⟩ := capText_ok success
      subst same
      exact ⟨⟨output, names, sources, parents, group, rowTexts, built, build_accepts built,
        originals_decoded built, namesRun, SourceRow.sourceRows_spec sourcesRun, parentsRun, groupRun,
        rowsRun, distinct, rfl, capped⟩⟩
    · simp [document, documentOf, built, distinct] at success

/-- A printed document certifies the original bytes unsatisfiable. -/
theorem document_original_unsat {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals
    functions file groupLabel labels text}
    (success : document limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨⟨output, _, _, _, _, _, built, _⟩⟩ := document_spec success
  exact build_original_unsat built

/-- A group row printed by `sapRow`: its unique closed reading, which holds in a
    source model exactly when the problem holds in the table model, and the
    `status(sap)` annotation naming every declaration. SAP for a printed
    document is `document_group_sap`. -/
theorem document_group {names : Body.Names} {problem : Fang.Equality.Problem} {groupLabel : String}
    {declarations : List Declaration} {parents : List String} {group : String}
    (parentsRun : (declarations.map Declaration.name).mapM parentText = .ok parents)
    (groupRun : sapRow names problem groupLabel parents = .ok group) :
    ∃ quoted body formula,
      group = groupRowText quoted body (groupAnnotation parents) ∧
      QuotedAtom quoted.toList groupLabel.toList ∧
      Group.groupFormula names problem = .ok formula ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧ formula.Within [] ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      (∀ {D : Type} (model : Source.Interpretation D),
        (∀ valuation, formula.Holds model valuation) ↔
          Fang.Equality.models (tableModel names.view model) problem) ∧
      DataText (groupAnnotation parents) (sapDatum (declarations.map Declaration.name)) := by
  unfold sapRow at groupRun
  obtain ⟨quoted, quotedRun, groupRun⟩ := bind_ok groupRun
  obtain ⟨body, bodyRun, groupRun⟩ := bind_ok groupRun
  have same := Except.ok.inj groupRun
  subst same
  obtain ⟨formula, formulaRun, parsed, closed, unique, meaning⟩ := Group.groupText_spec bodyRun
  exact ⟨quoted, body, formula, rfl, quote_grammar quotedRun, formulaRun, parsed, closed, unique,
    meaning, sap_annotation parentsRun⟩

/-- SAP for the group row of a printed document: the row is printed from the
    attached names and the prepared problem of an accepted pair, it has one
    reading, and if the original bytes have a model then that reading holds in
    some source model. -/
theorem document_group_sap {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
    groupLabel labels text}
    (success : document limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals functions file
      groupLabel labels = .ok text) :
    ∃ output names parents group quoted body formula,
      build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
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
    document_spec success
  obtain ⟨quoted, body, formula, printed, _, formulaRun, parsed, _, unique, _⟩ :=
    document_group parentsRun groupRun
  exact ⟨output, names, parents, group, quoted, body, formula, built, namesRun, parentsRun, groupRun,
    printed, parsed, unique, fun satisfiable => build_group_sap built namesRun formulaRun satisfiable⟩

/-- Each printed clause row follows from its parent rows; an input row from the
    prepared problem, which the group row states. -/
theorem row_local {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (built : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output)
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
  apply Local.step_local (build_row_checked built position) (tableModel names.view model)
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
theorem final_row_empty {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals output}
    (built : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ((rows output)[output.certificate.final]?).map Prod.snd = some [] ∧
      output.certificate.final + 1 = (rows output).length := by
  obtain ⟨checkedSteps, stepsLength, last, empty⟩ := retain_witness (build_witness built).2.2.2
  have clauses := (build_rows built).2
  have clausesLength := congrArg List.length clauses
  simp only [List.length_map] at clausesLength
  refine ⟨?_, by rw [clausesLength]; exact last⟩
  rw [← clauses] at empty
  simpa using empty

def outputNames (output : Expanded.Output) : Body.Names :=
  exportNames output.prepared.original.functions output.prepared.original.predicates
    output.prepared.functionArities output.prepared.predicateArities

def exportDocument (limit : Nat) (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Aeneas.Std.Usize)
    (file : String) : Except String String :=
  match build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | .error _ => .error "export-error: the certificate is not accepted for these bytes"
  | .ok output => documentOf output (outputNames output) file
      (Expanded.exportLabels output).1 (Expanded.exportLabels output).2

theorem exportDocument_spec {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file text}
    (success : exportDocument limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file =
      .ok text) :
    ∃ output, build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok output ∧
      DocumentFacts limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals
        (outputNames output) file (Expanded.exportLabels output).1 (Expanded.exportLabels output).2 text := by
  unfold exportDocument at success
  cases built : build limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals with
  | error reason => rw [built] at success; cases success
  | ok output =>
    rw [built] at success
    refine ⟨output, rfl, document_spec ?_⟩
    unfold document
    rw [built]
    exact success

theorem exportDocument_original_unsat {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals
    file text}
    (success : exportDocument limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file =
      .ok text) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes := by
  obtain ⟨output, built, _⟩ := exportDocument_spec success
  exact build_original_unsat built

end Fang.QuantifiedEqualityTstp.NamedExport
