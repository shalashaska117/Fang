/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import RowUniqueness

namespace Fang.TstpText

structure PrintedRow where
  name : String
  role : RowRole
  clause : List Source.Literal
  metadata : Datum

def PrintedRowText (text : String) (row : PrintedRow) : Prop :=
  AnnotatedRowText text row.name row.role row.clause row.metadata

inductive ParsedRows : List Char → List PrintedRow → Prop where
  | nil : ParsedRows [] []
  | cons {input rest row rows}
      (head : ParsedRow input row.name row.role row.clause row.metadata rest)
      (tail : ParsedRows rest rows) : ParsedRows input (row :: rows)

theorem ParsedRow.nonempty {input name role clause metadata rest}
    (parsed : ParsedRow input name role clause metadata rest) : input ≠ [] := by
  intro empty
  subst input
  obtain ⟨a, _, _, _, _, _, _, _, _, _, _, tag, _⟩ := parsed
  change none = some (TstpUnique.Token.atom "cnf", a) at tag
  contradiction

theorem ParsedRows.unique {input left right} (first : ParsedRows input left)
    (second : ParsedRows input right) : left = right := by
  induction first generalizing right with
  | nil =>
    cases second with
    | nil => rfl
    | cons head tail => exact False.elim (head.nonempty rfl)
  | @cons input rest row rows head tail ih =>
    cases second with
    | nil => exact False.elim (head.nonempty rfl)
    | @cons _ rest' row' rows' head' tail' =>
      obtain ⟨name, role, clause, metadata, residual⟩ := head.unique head'
      subst rest'
      have sameRow : row = row' := by
        cases row
        cases row'
        simp_all
      rw [sameRow, ih tail']

theorem printed_rows_parse {lines : List String} {rows : List PrintedRow}
    (grammar : Source.RelatedLists PrintedRowText lines rows) :
    ParsedRows (String.join lines).toList rows := by
  induction grammar with
  | nil => exact .nil
  | @cons line row lines rows head tail ih =>
    have parsed := head.prefix (String.join lines).toList
    have combined := ParsedRows.cons parsed ih
    simpa [String.join_cons, String.toList_append] using combined

theorem printed_rows_unique {leftLines rightLines : List String} {left right : List PrintedRow}
    (first : Source.RelatedLists PrintedRowText leftLines left)
    (second : Source.RelatedLists PrintedRowText rightLines right)
    (same : String.join leftLines = String.join rightLines) : left = right := by
  have parsed := printed_rows_parse first
  rw [same] at parsed
  exact parsed.unique (printed_rows_parse second)

theorem correspondence_printed_rows {problem label rows lines}
    (correspondence : Source.RelatedLists (RowCorrespondence problem label) rows lines) :
    ∃ printed, Source.RelatedLists PrintedRowText lines printed ∧
      Source.RelatedLists (fun row named =>
        named.name = row.name ∧ named.role = originRole row.origin ∧
        NamedClause problem row.clause named.clause ∧
        SourceMeaning problem label row.origin named.metadata) rows printed := by
  induction correspondence with
  | nil => exact ⟨[], .nil, .nil⟩
  | @cons row line rows lines head tail ih =>
    obtain ⟨clause, metadata, named, meaning, grammar⟩ := head
    obtain ⟨printed, textRows, meanings⟩ := ih
    exact ⟨⟨row.name, originRole row.origin, clause, metadata⟩ :: printed,
      .cons grammar textRows, .cons ⟨rfl, rfl, named, meaning⟩ meanings⟩

end Fang.TstpText
