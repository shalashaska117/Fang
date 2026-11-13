/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The derivation part of a version-8 TSTP document: one SAP group row followed
   by the annotated clause rows, with labels distinct across the whole document.
   Source rows are rendered by a separate module and passed in by label. -/
import ExpandedTrace
import EqualityLocal

namespace Fang.QuantifiedEqualityTstp.Expanded
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration TstpText

def groupAnnotation (parents : List String) : String :=
  Rows.call "inference" ["fang_preprocessing", Rows.bracket ["status(sap)"], Rows.bracket parents]

def groupDatum (parents : List String) : Datum :=
  .function "inference" [.atom "fang_preprocessing", .list [.function "status" [.atom "sap"]],
    .list (parents.map Datum.atom)]

def groupRowText (quoted body annotation : String) : String :=
  "fof(" ++ quoted ++ ",plain,(" ++ body ++ ")," ++ annotation ++ ").\n"

def groupRow (names : Body.Names) (problem : Fang.Equality.Problem) (groupLabel : String)
    (sources : List String) : Except String String := do
  let quoted ← TstpExport.quote groupLabel
  let body ← Group.groupText names problem
  let parents ← sources.mapM TstpExport.quote
  pure (groupRowText quoted body (groupAnnotation parents))

/-- Every label of the document: sources, the group, then one per clause row. -/
def documentLabels (sources : List String) (groupLabel : String) (labels : List String) : List String :=
  sources ++ groupLabel :: labels

def derivation (output : Output) (names : Body.Names) (sources : List String) (groupLabel : String)
    (labels : List String) : Except String String :=
  if !decide (documentLabels sources groupLabel labels).Nodup then
    .error "export-error: document labels are not distinct"
  else
    match groupRow names output.prepared.problem groupLabel sources,
        Rows.render names groupLabel labels (rows output) with
    | .ok group, .ok texts => .ok (group ++ String.join texts)
    | .error reason, _ => .error reason
    | .ok _, .error reason => .error reason

private theorem bind_ok {α β : Type} {action : Except String α}
    {next : α → Except String β} {result : β}
    (success : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error reason => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem quoted_parents {sources : List String} :
    ∀ {texts : List String}, sources.mapM TstpExport.quote = .ok texts →
      DataTexts texts (sources.map Datum.atom)
  := by
  induction sources with
  | nil =>
    intro texts success
    simp [pure, Except.pure] at success
    subst texts
    exact .nil
  | cons first rest ih =>
    intro texts success
    cases headRun : TstpExport.quote first with
    | error reason => simp [List.mapM_cons, headRun, bind, Except.bind] at success
    | ok head =>
      cases tailRun : rest.mapM TstpExport.quote with
      | error reason => simp [List.mapM_cons, headRun, tailRun, bind, Except.bind] at success
      | ok tail =>
        simp [List.mapM_cons, headRun, tailRun, bind, Except.bind, pure, Except.pure] at success
        subst texts
        exact .cons (quoted_data headRun) (ih tailRun)

theorem group_annotation {sources texts : List String}
    (quoted : sources.mapM TstpExport.quote = .ok texts) :
    DataText (groupAnnotation texts) (groupDatum sources) := by
  unfold groupAnnotation groupDatum Rows.call Rows.bracket
  exact .function (checked_lower "inference" (by decide)) (by simp)
    (.cons (.atom (checked_lower "fang_preprocessing" (by decide)))
      (.cons (.list (.cons (.function (checked_lower "status" (by decide)) (by simp)
          (.cons (.atom (checked_lower "sap" (by decide))) .nil)) .nil))
        (.cons (.list (quoted_parents quoted)) .nil)))

/-- Field grammar of the group row: quoted label, body read by the accepted
    version-7 formula grammar, and the `status(sap)` annotation naming every source. -/
theorem groupRow_spec {names problem groupLabel sources text}
    (success : groupRow names problem groupLabel sources = .ok text) :
    ∃ quoted body annotation formula,
      text = groupRowText quoted body annotation ∧
      QuotedAtom quoted.toList groupLabel.toList ∧
      Group.groupFormula names problem = .ok formula ∧
      FormulaText.ParsesFormula (Source.Grammar.spelling body) formula ∧ formula.Within [] ∧
      (∀ other, FormulaText.ParsesFormula (Source.Grammar.spelling body) other → other = formula) ∧
      (∀ {D : Type} (model : Source.Interpretation D),
        (∀ valuation, formula.Holds model valuation) ↔ Fang.Equality.models (tableModel names.view model) problem) ∧
      DataText annotation (groupDatum sources) := by
  unfold groupRow at success
  obtain ⟨quoted, quotedRun, success⟩ := bind_ok success
  obtain ⟨body, bodyRun, success⟩ := bind_ok success
  obtain ⟨parents, parentsRun, success⟩ := bind_ok success
  have same := Except.ok.inj success
  subst same
  obtain ⟨formula, formulaRun, parsed, closed, unique, meaning⟩ := Group.groupText_spec bodyRun
  exact ⟨quoted, body, _, formula, rfl, quote_grammar quotedRun, formulaRun, parsed, closed, unique,
    meaning, group_annotation parentsRun⟩

theorem derivation_spec {output names sources groupLabel labels text}
    (success : derivation output names sources groupLabel labels = .ok text) :
    (documentLabels sources groupLabel labels).Nodup ∧
      ∃ group texts, groupRow names output.prepared.problem groupLabel sources = .ok group ∧
        Rows.render names groupLabel labels (rows output) = .ok texts ∧
        text = group ++ String.join texts := by
  unfold derivation at success
  split at success
  · cases success
  rename_i distinct
  refine ⟨by simpa using distinct, ?_⟩
  split at success
  · rename_i group texts groupRun rowsRun
    cases success
    exact ⟨group, texts, groupRun, rowsRun, rfl⟩
  · cases success
  · cases success

/-- Each printed clause row follows from its parent rows; an input row from the
    prepared problem, which the group row states. -/
theorem row_local {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (built : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
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
theorem final_row_empty {bytes maximumBytes proof limits maximumPredicates maximumLiterals output}
    (built : build bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok output) :
    ((rows output)[output.certificate.final]?).map Prod.snd = some [] ∧
      output.certificate.final + 1 = (rows output).length := by
  obtain ⟨checkedSteps, stepsLength, last, empty⟩ := retain_witness (build_witness built).2.2.2
  have clauses := (build_rows built).2
  have clausesLength := congrArg List.length clauses
  simp only [List.length_map] at clausesLength
  refine ⟨?_, by rw [clausesLength]; exact last⟩
  rw [← clauses] at empty
  simpa using empty

#print axioms Fang.QuantifiedEqualityTstp.Expanded.quoted_parents
#print axioms Fang.QuantifiedEqualityTstp.Expanded.group_annotation
#print axioms Fang.QuantifiedEqualityTstp.Expanded.groupRow_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.derivation_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.row_local
#print axioms Fang.QuantifiedEqualityTstp.Expanded.final_row_empty

end Fang.QuantifiedEqualityTstp.Expanded
