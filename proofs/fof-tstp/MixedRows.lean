/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.FormulaRows
import SequenceUniqueness

namespace Fang.FofTstpText
open TstpText TstpUnique

inductive MixedRow where
  | cnf (row : TstpText.PrintedRow)
  | fof (name : String) (formula : NamedFOF.Formula) (metadata : Datum)

def MixedRowText (text : String) : MixedRow → Prop
  | .cnf row => PrintedRowText text row
  | .fof name formula metadata => FormulaRowText text name formula metadata

inductive ParsedMixedRow : List Char → MixedRow → List Char → Prop where
  | cnf {input row rest}
      (parsed : ParsedRow input row.name row.role row.clause row.metadata rest) :
      ParsedMixedRow input (.cnf row) rest
  | fof {input name formula metadata rest}
      (parsed : ParsedFormulaRow input name formula metadata rest) :
      ParsedMixedRow input (.fof name formula metadata) rest

theorem ParsedFormulaRow.nonempty {input name formula metadata rest}
    (parsed : ParsedFormulaRow input name formula metadata rest) : input ≠ [] := by
  intro empty
  subst input
  obtain ⟨a, _, _, _, _, _, _, _, _, _, _, _, tag, _⟩ := parsed
  change none = some (TstpUnique.Token.atom "fof", a) at tag
  contradiction

theorem ParsedFormulaRow.not_cnf {input name formula metadata rest cnfName role clause data suffix}
    (parsed : ParsedFormulaRow input name formula metadata rest)
    (other : ParsedRow input cnfName role clause data suffix) : False := by
  obtain ⟨a, _, _, _, _, _, _, _, _, _, _, _, tag, _⟩ := parsed
  obtain ⟨b, _, _, _, _, _, _, _, _, _, _, otherTag, _⟩ := other
  exact (by decide : "fof" ≠ "cnf")
    (TstpUnique.Token.atom.inj (readToken_unique tag otherTag).1)

theorem ParsedMixedRow.nonempty {input row rest} (parsed : ParsedMixedRow input row rest) :
    input ≠ [] := by
  cases parsed with
  | cnf body => exact body.nonempty
  | fof body => exact body.nonempty

theorem ParsedMixedRow.unique {input left right leftRest rightRest}
    (first : ParsedMixedRow input left leftRest) (second : ParsedMixedRow input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | @cnf row _ parsed =>
    cases second with
    | @cnf other _ otherParsed =>
      obtain ⟨name, role, clause, metadata, rest⟩ := parsed.unique otherParsed
      have same : row = other := by
        cases row
        cases other
        simp_all
      exact ⟨congrArg MixedRow.cnf same, rest⟩
    | fof other => exact False.elim (other.not_cnf parsed)
  | fof parsed =>
    cases second with
    | cnf other => exact False.elim (parsed.not_cnf other)
    | fof other =>
      obtain ⟨name, formula, metadata, rest⟩ := parsed.unique other
      cases name
      cases formula
      cases metadata
      exact ⟨rfl, rest⟩

theorem MixedRowText.prefix {text row} (grammar : MixedRowText text row) (suffix : List Char) :
    ParsedMixedRow (text.toList ++ suffix) row suffix := by
  cases row with
  | cnf row => exact .cnf (TstpText.AnnotatedRowText.prefix grammar suffix)
  | fof name formula metadata => exact .fof (FormulaRowText.prefix grammar suffix)

inductive ParsedMixedRows : List Char → List MixedRow → Prop where
  | nil : ParsedMixedRows [] []
  | cons {input rest row rows}
      (head : ParsedMixedRow input row rest) (tail : ParsedMixedRows rest rows) :
      ParsedMixedRows input (row :: rows)

theorem ParsedMixedRows.unique {input left right} (first : ParsedMixedRows input left)
    (second : ParsedMixedRows input right) : left = right := by
  induction first generalizing right with
  | nil =>
    cases second with
    | nil => rfl
    | cons head _ => exact False.elim (head.nonempty rfl)
  | cons head tail ih =>
    cases second with
    | nil => exact False.elim (head.nonempty rfl)
    | cons otherHead otherTail =>
      obtain ⟨sameRow, sameRest⟩ := head.unique otherHead
      cases sameRest
      rw [sameRow, ih otherTail]

theorem mixed_rows_parse {lines rows}
    (grammar : Source.RelatedLists MixedRowText lines rows) :
    ParsedMixedRows (String.join lines).toList rows := by
  induction grammar with
  | nil => exact .nil
  | @cons line row lines rows head tail ih =>
    have parsed := MixedRowText.prefix head (String.join lines).toList
    have combined := ParsedMixedRows.cons parsed ih
    simpa [String.join_cons, String.toList_append] using combined

theorem mixed_rows_unique {leftLines rightLines left right}
    (first : Source.RelatedLists MixedRowText leftLines left)
    (second : Source.RelatedLists MixedRowText rightLines right)
    (same : String.join leftLines = String.join rightLines) : left = right := by
  have parsed := mixed_rows_parse first
  rw [same] at parsed
  exact parsed.unique (mixed_rows_parse second)

end Fang.FofTstpText
