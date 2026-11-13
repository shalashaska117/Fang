/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import AnnotatedRows
import Rows
import SourceLink

namespace Fang.TstpText

/-- Interpret numeric symbols by the exact retained table name. This is a
semantic model construction, not another parser or production algorithm. -/
def tableModel {D : Type} (problem : TstpExport.NamedProblem)
    (model : Source.Interpretation D) : Fang.Interpretation D where
  function index := model.function (Frontend.tableName problem.functions index)
  predicate index := model.predicate (Frontend.tableName problem.predicates index)

theorem SymbolText.table_name {symbols index arity name}
    (h : SymbolText symbols index arity name) :
    Frontend.tableName symbols index = name := by
  obtain ⟨value, found, same, _⟩ := h.entry
  simp [Frontend.tableName, found, same]

mutual
theorem NamedTerm.eval {problem : TstpExport.NamedProblem} {value named}
    (h : NamedTerm problem.functions value named) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    named.eval model valuation =
      value.eval (tableModel problem model) (fun index => valuation s!"X{index}") := by
  cases h with
  | «variable» index => simp only [Source.Term.eval, Fang.Term.eval]
  | application symbol children =>
    simp only [Source.Term.eval, Fang.Term.eval, tableModel]
    rw [symbol.table_name]
    exact congrArg _ (NamedTerms.eval children model valuation)
termination_by sizeOf value

theorem NamedTerms.eval {problem : TstpExport.NamedProblem} {values named}
    (h : NamedTerms problem.functions values named) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    named.map (Source.Term.eval model valuation) =
      values.map (Fang.Term.eval (tableModel problem model)
        (fun index => valuation s!"X{index}")) := by
  cases h with
  | nil => rfl
  | cons head tail =>
    simp only [List.map_cons, NamedTerm.eval head model valuation,
      NamedTerms.eval tail model valuation]
termination_by sizeOf values
end

theorem NamedLiteral.holds {problem : TstpExport.NamedProblem} {value named}
    (h : NamedLiteral problem value named) {D : Type}
    (model : Source.Interpretation D) (valuation : String → D) :
    named.Holds model valuation ↔
      value.Holds (tableModel problem model) (fun index => valuation s!"X{index}") := by
  simp only [Source.Literal.Holds, Fang.Literal.Holds, Fang.Atom.Holds, tableModel]
  rw [h.polarity, h.predicate.table_name, h.arguments.eval model valuation]
  rfl

/-- Universal closure is preserved: every named valuation is pulled back
along the actual X{id} variable names. No finite-domain restriction is used. -/
theorem NamedClause.valid {problem : TstpExport.NamedProblem} {value named}
    (h : NamedClause problem value named) {D : Type}
    (model : Source.Interpretation D) (name : String)
    (valid : value.Valid (tableModel problem model)) :
    (Source.Clause.mk name named).Valid model := by
  intro valuation
  obtain ⟨literal, member, holds⟩ := valid (fun index => valuation s!"X{index}")
  obtain ⟨output, outputMember, correspondence⟩ := h.member_left member
  exact ⟨output, outputMember, (correspondence.holds model valuation).mpr holds⟩

def SemanticRow {D : Type} (problem : TstpExport.NamedProblem) (fileLabel : String)
    (model : Source.Interpretation D) (row : TstpExport.Row) (text : String) : Prop :=
  ∃ named sourceData, NamedClause problem row.clause named ∧
    SourceMeaning problem fileLabel row.origin sourceData ∧
    AnnotatedRowText text row.name (originRole row.origin) named sourceData ∧
    (Source.Clause.mk row.name named).Valid model

theorem rows_semantics {problem : TstpExport.NamedProblem} {fileLabel : String}
    {rows : List TstpExport.Row} {lines : List String}
    (h : Source.RelatedLists (RowCorrespondence problem fileLabel) rows lines)
    {D : Type} (model : Source.Interpretation D)
    (valid : ∀ row ∈ rows, row.clause.Valid (tableModel problem model)) :
    Source.RelatedLists (SemanticRow problem fileLabel model) rows lines := by
  induction h with
  | nil => exact .nil
  | @cons row line rows lines correspondence tail ih =>
    obtain ⟨named, data, namedClause, source, grammar⟩ := correspondence
    exact .cons
      ⟨named, data, namedClause, source, grammar,
        namedClause.valid model row.name (valid row (by simp))⟩
      (ih (fun row member => valid row (List.mem_cons_of_mem _ member)))

/-- Conditional composition with the independently stated typed derivation.
The premise is explicit: this theorem does not prove the actual builder. -/
theorem render_derivation_valid (fileLabel : String) (exported : TstpExport.Export)
    {text : String} (rendered : TstpExport.render fileLabel exported = .ok text)
    (derivation : TstpExport.Derivation exported.signature exported.rows)
    {D : Type} (model : Source.Interpretation D)
    (original : exported.signature.signature.problem.Models (tableModel exported.signature model)) :
    ∃ lines, text = String.join lines ∧
      Source.RelatedLists (SemanticRow exported.signature fileLabel model) exported.rows lines ∧
      text.utf8ByteSize ≤ 16 * 1024 * 1024 := by
  obtain ⟨lines, joined, correspondence, size⟩ :=
    render_correspondence fileLabel exported rendered
  refine ⟨lines, joined, rows_semantics correspondence model ?_, size⟩
  exact TstpExport.derivation_valid _ _ _ original derivation

/-- Every model of the original named input satisfies each rendered clause,
provided the explicit typed-derivation premise. The actual decoder supplies
the source/table connection; no text-parser uniqueness is assumed here. -/
theorem render_original_models {input text : String}
    (fileLabel : String) (exported : TstpExport.Export)
    (decoded : TstpExport.decodeNamed input = .ok exported.signature)
    (rendered : TstpExport.render fileLabel exported = .ok text)
    (derivation : TstpExport.Derivation exported.signature exported.rows) :
    ∃ original, Source.Grammar.Parses (Source.Grammar.spelling input) original ∧
      ∀ (D : Type) (model : Source.Interpretation D), original.Models model →
        ∃ lines, text = String.join lines ∧
          Source.RelatedLists (SemanticRow exported.signature fileLabel model)
            exported.rows lines ∧ text.utf8ByteSize ≤ 16 * 1024 * 1024 := by
  obtain ⟨original, state, parsed, encoding, functions, predicates, _⟩ :=
    TstpExport.decodeNamed_source decoded
  refine ⟨original, parsed, ?_⟩
  intro D model models
  apply render_derivation_valid fileLabel exported rendered derivation model
  have same : tableModel exported.signature model =
      model.toNumeric (Frontend.symbolsFrom state) := by
    simp [tableModel, Source.Interpretation.toNumeric, Frontend.symbolsFrom, functions, predicates]
  rw [same]
  intro clause member
  obtain ⟨named, namedMember, variables, relation⟩ := encoding.clauses.member_right member
  exact relation.valid_toNumeric model (models named namedMember)

end Fang.TstpText
