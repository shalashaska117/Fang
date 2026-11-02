/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.FormulaMeaning
import AnnotatedRows

namespace Fang.FofTstpText
open TstpText

inductive FormulaRowText : String → String → NamedFOF.Formula → Datum → Prop where
  | row {quotedName name bodyText body sourceText sourceData}
      (label : QuotedAtom quotedName.toList name.toList) (formula : FormulaText bodyText body)
      (annotation : DataText sourceText sourceData) (kind : SourceRecord sourceData) :
      FormulaRowText ("fof(" ++ quotedName ++ ",axiom,(" ++ bodyText ++ ")," ++ sourceText ++ ").\n")
        name body sourceData

theorem FormulaRowText.spelling_eq {left right name formula metadata}
    (grammar : FormulaRowText left name formula metadata) (same : left = right) :
    FormulaRowText right name formula metadata := same ▸ grammar

theorem cnf_row_spelling {left right name role clause metadata}
    (grammar : AnnotatedRowText left name role clause metadata) (same : left = right) :
    AnnotatedRowText right name role clause metadata := same ▸ grammar

theorem source_formula_correspondence {problem : TstpExport.NamedProblem}
    {fileLabel sourceName : String} {body : GroundFOF.Formula} {text : String}
    (printed : FofTstpExport.sourceFormula problem fileLabel sourceName body = .ok text) :
    ∃ named, NamedFormula problem body named ∧ FormulaRowText text sourceName named
      (.function "file" [.atom fileLabel, .atom sourceName]) := by
  cases nameEq : TstpExport.quote sourceName with
  | error error => simp [FofTstpExport.sourceFormula, nameEq, bind, Except.bind] at printed
  | ok name =>
    cases bodyEq : FofTstpExport.formula problem body with
    | error error => simp [FofTstpExport.sourceFormula, nameEq, bodyEq, bind, Except.bind] at printed
    | ok bodyText =>
      cases labelEq : TstpExport.quote fileLabel with
      | error error => simp [FofTstpExport.sourceFormula, nameEq, bodyEq, labelEq, bind, Except.bind] at printed
      | ok label =>
        have shape : "fof(" ++ name ++ ",axiom,(" ++ bodyText ++ "),file(" ++ label ++ "," ++ name ++ ")).\n" = text := by
          simpa [FofTstpExport.sourceFormula, nameEq, bodyEq, labelEq, bind, Except.bind, pure, Except.pure] using printed
        subst text
        obtain ⟨named, relation, grammar⟩ := formula_correspondence body bodyEq
        have annotation := function_two "file" (by decide) (quoted_data labelEq) (quoted_data nameEq)
        refine ⟨named, relation, ?_⟩
        exact (FormulaRowText.row (quote_grammar nameEq) grammar annotation
          (.file fileLabel sourceName)).spelling_eq (by string_shape)

def clausificationData (leaf : FofTstpExport.Leaf) : Datum :=
  .function "inference" [.atom "fang_clausify",
    .list [statusThm, .function "source_index" [.natural leaf.declaration],
      .function "clause_index" [.natural leaf.localClause]], .list [.atom leaf.sourceName]]

theorem clausification_record (leaf : FofTstpExport.Leaf) : SourceRecord (clausificationData leaf) :=
  .inference "fang_clausify" _ [leaf.sourceName]

theorem clausified_row_correspondence {problem : TstpExport.NamedProblem}
    (leaf : FofTstpExport.Leaf) {text : String}
    (printed : FofTstpExport.clausifiedRow problem leaf = .ok text) :
    ∃ named, NamedClause problem leaf.clause named ∧
      AnnotatedRowText text leaf.rawName .plain named (clausificationData leaf) := by
  cases nameEq : TstpExport.quote leaf.rawName with
  | error error => simp [FofTstpExport.clausifiedRow, nameEq, bind, Except.bind] at printed
  | ok name =>
    cases clauseEq : TstpExport.clause problem leaf.clause with
    | error error => simp [FofTstpExport.clausifiedRow, nameEq, clauseEq, bind, Except.bind] at printed
    | ok clauseText =>
      cases parentEq : TstpExport.quote leaf.sourceName with
      | error error => simp [FofTstpExport.clausifiedRow, nameEq, clauseEq, parentEq, bind, Except.bind] at printed
      | ok parent =>
        simp [FofTstpExport.clausifiedRow, nameEq, clauseEq, parentEq, bind, Except.bind, pure, Except.pure] at printed
        subst text
        obtain ⟨named, relation, grammar⟩ := clause_byte_correspondence leaf.clause clauseEq
        have sourceIndex := function_one "source_index" (by decide) (.natural (natural_spelling leaf.declaration))
        have clauseIndex := function_one "clause_index" (by decide) (.natural (natural_spelling leaf.localClause))
        have annotation := inference_text "fang_clausify" (by decide)
          (.cons status_text (.cons sourceIndex (.cons clauseIndex .nil)))
          (.cons (quoted_data parentEq) .nil)
        refine ⟨named, relation, ?_⟩
        exact cnf_row_spelling (AnnotatedRowText.row .plain (quote_grammar nameEq)
          grammar annotation (clausification_record leaf)) (by string_shape)

end Fang.FofTstpText
