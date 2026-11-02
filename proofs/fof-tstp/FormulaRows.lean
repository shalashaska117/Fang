/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.CompoundPrefix
import Fang.FOF.TSTP.FofRows
import RowUniqueness

namespace Fang.FofTstpText
open TstpText TstpUnique FofTstpPrefix

/-- Consuming grammar for an emitted FOF axiom, including its metadata and
    final newline. Formula tokens use the FOF extension; metadata uses the
    unchanged annotation grammar. -/
def ParsedFormulaRow (input : List Char) (name : String)
    (formula : NamedFOF.Formula) (metadata : Datum) (rest : List Char) : Prop :=
  ∃ a b c d e f g h i j k l,
    readToken input = some (.atom "fof", a) ∧
    readToken a = some (.punctuation '(', b) ∧
    readToken b = some (.atom name, c) ∧
    readToken c = some (.punctuation ',', d) ∧
    readToken d = some (.atom "axiom", e) ∧
    readToken e = some (.punctuation ',', f) ∧
    readToken f = some (.punctuation '(', g) ∧
    FormulaPrefix g formula h ∧
    read h = some (.base (.punctuation ')'), i) ∧
    readToken i = some (.punctuation ',', j) ∧
    ParsedData j metadata k ∧
    readToken k = some (.punctuation ')', l) ∧
    readToken l = some (.punctuation '.', '\n' :: rest)

theorem ParsedFormulaRow.unique {input leftName rightName leftFormula rightFormula
    leftData rightData leftRest rightRest}
    (first : ParsedFormulaRow input leftName leftFormula leftData leftRest)
    (second : ParsedFormulaRow input rightName rightFormula rightData rightRest) :
    leftName = rightName ∧ leftFormula = rightFormula ∧ leftData = rightData ∧
      leftRest = rightRest := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l,
    tag, openRow, name, commaName, role, commaRole, openBody, body, closeBody,
    commaBody, data, closeRow, period⟩ := first
  obtain ⟨a', b', c', d', e', f', g', h', i', j', k', l',
    tag', openRow', name', commaName', role', commaRole', openBody', body', closeBody',
    commaBody', data', closeRow', period'⟩ := second
  have same := (readToken_unique tag tag').2
  subst a'
  have same := (readToken_unique openRow openRow').2
  subst b'
  obtain ⟨names, same⟩ := readToken_unique name name'
  have names := TstpUnique.Token.atom.inj names
  subst rightName
  subst c'
  have same := (readToken_unique commaName commaName').2
  subst d'
  have same := (readToken_unique role role').2
  subst e'
  have same := (readToken_unique commaRole commaRole').2
  subst f'
  have same := (readToken_unique openBody openBody').2
  subst g'
  obtain ⟨formulas, same⟩ := body.unique body'
  subst rightFormula
  subst h'
  have same := (read_unique closeBody closeBody').2
  subst i'
  have same := (readToken_unique commaBody commaBody').2
  subst j'
  obtain ⟨values, same⟩ := data.unique data'
  subst rightData
  subst k'
  have same := (readToken_unique closeRow closeRow').2
  subst l'
  exact ⟨rfl, rfl, rfl, (List.cons.inj (readToken_unique period period').2).2⟩

theorem FormulaRowText.prefix {text name formula metadata}
    (grammar : FormulaRowText text name formula metadata) (suffix : List Char) :
    ParsedFormulaRow (text.toList ++ suffix) name formula metadata suffix := by
  cases grammar with
  | @row quotedName name bodyText body sourceText sourceData label formula annotation kind =>
    let l := '.' :: '\n' :: suffix
    let k := ')' :: l
    let j := sourceText.toList ++ k
    let i := ',' :: j
    let bodySuffix := ')' :: i
    let g := bodyText.toList ++ bodySuffix
    let f := '(' :: g
    let e := ',' :: f
    let d := "axiom".toList ++ e
    let c := ',' :: d
    let b := quotedName.toList ++ c
    let a := '(' :: b
    have closing := read_old (readToken_punctuation ')' (by decide) i)
    obtain ⟨middle, parsedBody, bodyEnd⟩ := formula_text_prefix formula bodySuffix
      (punctuation_boundary ')' (by decide) i) (by
        intro rest opening
        have impossible := (read_unique closing opening).1
        cases impossible)
    refine ⟨a, b, c, d, e, f, g, middle, i, j, k, l,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, parsedBody, bodyEnd.trans closing, ?_, ?_, ?_, ?_⟩
    · have tag := readToken_atomic (checked_lower "fof" (by decide)) a
        (punctuation_boundary '(' (by decide) b)
      simpa [a, b, c, d, e, f, g, bodySuffix, i, j, k, l,
        String.toList_append, List.append_assoc] using tag
    · exact readToken_punctuation '(' (by decide) b
    · simpa [b] using readToken_quoted label c
    · exact readToken_punctuation ',' (by decide) d
    · exact readToken_atomic (checked_lower "axiom" (by decide)) e
        (punctuation_boundary ',' (by decide) f)
    · exact readToken_punctuation ',' (by decide) f
    · exact readToken_punctuation '(' (by decide) g
    · exact readToken_punctuation ',' (by decide) j
    · exact TstpUnique.DataText.prefix annotation k (.paren l)
    · exact readToken_punctuation ')' (by decide) l
    · exact readToken_punctuation '.' (by decide) ('\n' :: suffix)

theorem FormulaRowText.prefix_unique {left right leftName rightName leftFormula rightFormula
    leftData rightData leftSuffix rightSuffix}
    (first : FormulaRowText left leftName leftFormula leftData)
    (second : FormulaRowText right rightName rightFormula rightData)
    (same : left.toList ++ leftSuffix = right.toList ++ rightSuffix) :
    leftName = rightName ∧ leftFormula = rightFormula ∧ leftData = rightData ∧
      leftSuffix = rightSuffix := by
  have parsed := first.prefix leftSuffix
  rw [same] at parsed
  exact parsed.unique (second.prefix rightSuffix)

theorem source_formula_parses {problem fileLabel sourceName body text}
    (printed : FofTstpExport.sourceFormula problem fileLabel sourceName body = .ok text)
    (suffix : List Char) :
    ∃ named, NamedFormula problem body named ∧
      ParsedFormulaRow (text.toList ++ suffix) sourceName named
        (.function "file" [.atom fileLabel, .atom sourceName]) suffix := by
  obtain ⟨named, relation, grammar⟩ := source_formula_correspondence printed
  exact ⟨named, relation, grammar.prefix suffix⟩

end Fang.FofTstpText
