/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import SourceMetadata

namespace Fang.TstpText

inductive RowRole where
  | axiom | plain

def RowRole.text : RowRole → String
  | .axiom => "axiom"
  | .plain => "plain"

def originRole : TstpExport.Origin → RowRole
  | .input _ _ => .axiom
  | _ => .plain

/-- The emitted annotated-CNF subset of the retained BNF. The clause parser
consumes the closing parenthesis before the source comma. This is a grammar
derivation with named fields, not yet a unique full-row decoder. -/
inductive AnnotatedRowText :
    String → String → RowRole → List Source.Literal → Datum → Prop where
  | row {quotedName name bodyText body sourceText sourceData} (role : RowRole)
      (label : QuotedAtom quotedName.toList name.toList)
      (formula : ClauseBytesParse (Source.Grammar.spelling bodyText) body)
      (annotation : DataText sourceText sourceData) (kind : SourceRecord sourceData) :
      AnnotatedRowText
        ("cnf(" ++ quotedName ++ "," ++ role.text ++ ",(" ++ bodyText ++ ")," ++ sourceText ++ ").\n")
        name role body sourceData

def RowCorrespondence (problem : TstpExport.NamedProblem) (fileLabel : String)
    (row : TstpExport.Row) (text : String) : Prop :=
  ∃ named sourceData, NamedClause problem row.clause named ∧
    SourceMeaning problem fileLabel row.origin sourceData ∧
    AnnotatedRowText text row.name (originRole row.origin) named sourceData

theorem row_correspondence {problem : TstpExport.NamedProblem} (fileLabel : String)
    (row : TstpExport.Row) {text : String}
    (accepted : TstpExport.renderRow problem fileLabel row = .ok text) :
    RowCorrespondence problem fileLabel row text := by
  cases hn : TstpExport.quote row.name with
  | error e => simp [TstpExport.renderRow, hn, bind, Except.bind] at accepted
  | ok nameText =>
    cases hc : TstpExport.clause problem row.clause with
    | error e => simp [TstpExport.renderRow, hn, hc, bind, Except.bind] at accepted
    | ok clauseText =>
      cases hs : TstpExport.source problem fileLabel row.origin with
      | error e => simp [TstpExport.renderRow, hn, hc, hs, bind, Except.bind] at accepted
      | ok sourceText =>
        simp [TstpExport.renderRow, hn, hc, hs, bind, Except.bind, pure, Except.pure] at accepted
        have shape :
            "cnf(" ++ nameText ++ "," ++ (originRole row.origin).text ++ ",(" ++
              clauseText ++ ")," ++ sourceText ++ ").\n" = text := by
          cases ho : row.origin <;> simpa [ho, originRole, RowRole.text] using accepted
        clear accepted
        subst text
        obtain ⟨named, correspondence, grammar⟩ := clause_byte_correspondence row.clause hc
        obtain ⟨sourceData, sourceMeaning, sourceGrammar⟩ := source_correspondence fileLabel row.origin hs
        exact ⟨named, sourceData, correspondence, sourceMeaning,
          .row _ (quote_grammar hn) grammar sourceGrammar sourceMeaning.record⟩

theorem row_list_correspondence {problem : TstpExport.NamedProblem} (fileLabel : String)
    (rows : List TstpExport.Row) {texts : List String}
    (accepted : rows.mapM (TstpExport.renderRow problem fileLabel) = .ok texts) :
    Source.RelatedLists (RowCorrespondence problem fileLabel) rows texts := by
  induction rows generalizing texts with
  | nil =>
    simp [pure, Except.pure] at accepted
    subst texts
    exact .nil
  | cons first rest ih =>
    cases hf : TstpExport.renderRow problem fileLabel first with
    | error e => simp [List.mapM_cons, hf, bind, Except.bind] at accepted
    | ok text =>
      cases ht : rest.mapM (TstpExport.renderRow problem fileLabel) with
      | error e => simp [List.mapM_cons, hf, ht, bind, Except.bind] at accepted
      | ok tail =>
        simp [List.mapM_cons, hf, ht, bind, Except.bind, pure, Except.pure] at accepted
        subst texts
        exact .cons (row_correspondence fileLabel first hf) (ih ht)

theorem render_correspondence (fileLabel : String) (exported : TstpExport.Export)
    {text : String} (accepted : TstpExport.render fileLabel exported = .ok text) :
    ∃ lines, text = String.join lines ∧
      Source.RelatedLists (RowCorrespondence exported.signature fileLabel) exported.rows lines ∧
      text.utf8ByteSize ≤ 16 * 1024 * 1024 := by
  cases hl : TstpExport.quote fileLabel with
  | error e => simp [TstpExport.render, hl, discard, Functor.mapConst, Functor.map, Except.map,
      bind, Except.bind] at accepted
  | ok label =>
    cases hr : exported.rows.mapM (TstpExport.renderRow exported.signature fileLabel) with
    | error e => simp [TstpExport.render, hl, hr, discard, Functor.mapConst, Functor.map, Except.map,
        bind, Except.bind, pure, Except.pure] at accepted
    | ok lines =>
      by_cases large : (String.join lines).utf8ByteSize > 16 * 1024 * 1024
      · simp [TstpExport.render, hl, hr, large, discard, Functor.mapConst, Functor.map, Except.map,
          throw, throwThe, bind, Except.bind, pure, Except.pure] at accepted
      · simp [TstpExport.render, hl, hr, large, discard, Functor.mapConst, Functor.map, Except.map,
          bind, Except.bind, pure, Except.pure] at accepted
        subst text
        exact ⟨lines, rfl, row_list_correspondence fileLabel exported.rows hr, by omega⟩

end Fang.TstpText
