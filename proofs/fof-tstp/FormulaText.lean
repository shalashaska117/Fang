/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TstpExport
import LiteralParsing

namespace Fang.FofTstpText
open TstpText

/-- Numeric formula IDs and arguments denote exactly the retained source names.
    This is a relation on syntax, not another printer or normalization routine. -/
inductive NamedFormula (problem : TstpExport.NamedProblem) :
    GroundFOF.Formula → NamedFOF.Formula → Prop where
  | atom {predicate arguments name named}
      (symbol : SymbolText problem.predicates predicate arguments.length name)
      (children : NamedTerms problem.functions arguments named) :
      NamedFormula problem (.atom ⟨predicate, arguments⟩) (.atom name named)
  | truth : NamedFormula problem .truth .truth
  | falsity : NamedFormula problem .falsity .falsity
  | neg {body named} (child : NamedFormula problem body named) :
      NamedFormula problem (.neg body) (.neg named)
  | conj {left right first second} (a : NamedFormula problem left first)
      (b : NamedFormula problem right second) :
      NamedFormula problem (.conj left right) (.conj first second)
  | disj {left right first second} (a : NamedFormula problem left first)
      (b : NamedFormula problem right second) :
      NamedFormula problem (.disj left right) (.disj first second)
  | implies {left right first second} (a : NamedFormula problem left first)
      (b : NamedFormula problem right second) :
      NamedFormula problem (.implies left right) (.implies first second)

/-- Fully parenthesized FOF bodies, with atoms interpreted by the existing
    independent byte grammar. Row framing and unique consumption are separate. -/
inductive FormulaText : String → NamedFOF.Formula → Prop where
  | atom {text name arguments}
      (body : LiteralBytesParse (Source.Grammar.spelling text) ⟨true, name, arguments⟩) :
      FormulaText text (.atom name arguments)
  | truth : FormulaText "$true" .truth
  | falsity : FormulaText "$false" .falsity
  | neg {text body} (child : FormulaText text body) : FormulaText ("~(" ++ text ++ ")") (.neg body)
  | conj {left right first second} (a : FormulaText left first) (b : FormulaText right second) :
      FormulaText ("(" ++ left ++ " & " ++ right ++ ")") (.conj first second)
  | disj {left right first second} (a : FormulaText left first) (b : FormulaText right second) :
      FormulaText ("(" ++ left ++ " | " ++ right ++ ")") (.disj first second)
  | implies {left right first second} (a : FormulaText left first) (b : FormulaText right second) :
      FormulaText ("(" ++ left ++ " => " ++ right ++ ")") (.implies first second)

theorem formula_correspondence {problem : TstpExport.NamedProblem}
    (value : GroundFOF.Formula) {text : String}
    (printed : FofTstpExport.formula problem value = .ok text) :
    ∃ named, NamedFormula problem value named ∧ FormulaText text named := by
  induction value generalizing text with
  | atom atom =>
    obtain ⟨named, relation, grammar⟩ := literal_byte_correspondence
      (problem := problem) ⟨true, atom⟩ printed
    rcases named with ⟨positive, name, args⟩
    have polarity : positive = true := relation.polarity
    subst positive
    exact ⟨.atom name args, .atom relation.predicate relation.arguments, .atom grammar⟩
  | truth =>
    have same : "$true" = text := Except.ok.inj printed
    subst text
    exact ⟨.truth, .truth, .truth⟩
  | falsity =>
    have same : "$false" = text := Except.ok.inj printed
    subst text
    exact ⟨.falsity, .falsity, .falsity⟩
  | neg body ih =>
    cases result : FofTstpExport.formula problem body with
    | error error => simp [FofTstpExport.formula, result, bind, Except.bind] at printed
    | ok child =>
      obtain ⟨named, relation, grammar⟩ := ih result
      have same : "~(" ++ child ++ ")" = text := by
        simpa [FofTstpExport.formula, result, bind, Except.bind, pure, Except.pure] using printed
      subst text
      exact ⟨.neg named, .neg relation, .neg grammar⟩
  | conj left right leftIH rightIH =>
    cases first : FofTstpExport.formula problem left with
    | error error => simp [FofTstpExport.formula, first, bind, Except.bind] at printed
    | ok firstText =>
      cases second : FofTstpExport.formula problem right with
      | error error => simp [FofTstpExport.formula, first, second, bind, Except.bind] at printed
      | ok secondText =>
        obtain ⟨firstNamed, firstRelation, firstGrammar⟩ := leftIH first
        obtain ⟨secondNamed, secondRelation, secondGrammar⟩ := rightIH second
        have same : "(" ++ firstText ++ " & " ++ secondText ++ ")" = text := by
          simpa [FofTstpExport.formula, first, second, bind, Except.bind, pure, Except.pure] using printed
        subst text
        exact ⟨.conj firstNamed secondNamed, .conj firstRelation secondRelation,
          .conj firstGrammar secondGrammar⟩
  | disj left right leftIH rightIH =>
    cases first : FofTstpExport.formula problem left with
    | error error => simp [FofTstpExport.formula, first, bind, Except.bind] at printed
    | ok firstText =>
      cases second : FofTstpExport.formula problem right with
      | error error => simp [FofTstpExport.formula, first, second, bind, Except.bind] at printed
      | ok secondText =>
        obtain ⟨firstNamed, firstRelation, firstGrammar⟩ := leftIH first
        obtain ⟨secondNamed, secondRelation, secondGrammar⟩ := rightIH second
        have same : "(" ++ firstText ++ " | " ++ secondText ++ ")" = text := by
          simpa [FofTstpExport.formula, first, second, bind, Except.bind, pure, Except.pure] using printed
        subst text
        exact ⟨.disj firstNamed secondNamed, .disj firstRelation secondRelation,
          .disj firstGrammar secondGrammar⟩
  | implies left right leftIH rightIH =>
    cases first : FofTstpExport.formula problem left with
    | error error => simp [FofTstpExport.formula, first, bind, Except.bind] at printed
    | ok firstText =>
      cases second : FofTstpExport.formula problem right with
      | error error => simp [FofTstpExport.formula, first, second, bind, Except.bind] at printed
      | ok secondText =>
        obtain ⟨firstNamed, firstRelation, firstGrammar⟩ := leftIH first
        obtain ⟨secondNamed, secondRelation, secondGrammar⟩ := rightIH second
        have same : "(" ++ firstText ++ " => " ++ secondText ++ ")" = text := by
          simpa [FofTstpExport.formula, first, second, bind, Except.bind, pure, Except.pure] using printed
        subst text
        exact ⟨.implies firstNamed secondNamed, .implies firstRelation secondRelation,
          .implies firstGrammar secondGrammar⟩

end Fang.FofTstpText
