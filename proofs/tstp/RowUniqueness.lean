/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import BodyBridge
import AnnotationMembership
import AnnotatedRows

namespace Fang.TstpText

open TstpUnique

/-- A consuming row grammar. It reads the fixed row header, the established
first-order body, source metadata, and the actual final newline. -/
def ParsedRow (input : List Char) (name : String) (role : RowRole)
    (clause : List Source.Literal) (metadata : Datum) (rest : List Char) : Prop :=
  ∃ a b c d e f g h i j k,
    readToken input = some (.atom "cnf", a) ∧
    readToken a = some (.punctuation '(', b) ∧
    readToken b = some (.atom name, c) ∧
    readToken c = some (.punctuation ',', d) ∧
    readToken d = some (.atom role.text, e) ∧
    readToken e = some (.punctuation ',', f) ∧
    readToken f = some (.punctuation '(', g) ∧
    TstpBody.BodyPrefix g clause h ∧
    readToken h = some (.punctuation ',', i) ∧
    ParsedData i metadata j ∧
    readToken j = some (.punctuation ')', k) ∧
    readToken k = some (.punctuation '.', '\n' :: rest)

theorem role_text_injective {left right : RowRole} (same : left.text = right.text) :
    left = right := by
  cases left <;> cases right <;> simp_all [RowRole.text]

theorem ParsedRow.unique {input leftName rightName leftRole rightRole leftClause rightClause
    leftData rightData leftRest rightRest}
    (first : ParsedRow input leftName leftRole leftClause leftData leftRest)
    (second : ParsedRow input rightName rightRole rightClause rightData rightRest) :
    leftName = rightName ∧ leftRole = rightRole ∧ leftClause = rightClause ∧
      leftData = rightData ∧ leftRest = rightRest := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j, k,
    tag, openRow, name, commaName, role, commaRole, openBody, body, commaBody, data, closeRow, period⟩ := first
  obtain ⟨a', b', c', d', e', f', g', h', i', j', k',
    tag', openRow', name', commaName', role', commaRole', openBody', body', commaBody', data', closeRow', period'⟩ := second
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
  obtain ⟨roles, same⟩ := readToken_unique role role'
  have roles := role_text_injective (TstpUnique.Token.atom.inj roles)
  subst rightRole
  subst e'
  have same := (readToken_unique commaRole commaRole').2
  subst f'
  have same := (readToken_unique openBody openBody').2
  subst g'
  obtain ⟨clauses, same⟩ := body.unique body'
  subst rightClause
  subst h'
  have same := (readToken_unique commaBody commaBody').2
  subst i'
  obtain ⟨values, same⟩ := data.unique data'
  subst rightData
  subst j'
  have same := (readToken_unique closeRow closeRow').2
  subst k'
  have same := (List.cons.inj (readToken_unique period period').2).2
  exact ⟨rfl, rfl, rfl, rfl, same⟩

theorem AnnotatedRowText.prefix {text name role clause metadata}
    (grammar : AnnotatedRowText text name role clause metadata) (suffix : List Char) :
    ParsedRow (text.toList ++ suffix) name role clause metadata suffix := by
  cases grammar with
  | @row quotedName name bodyText body sourceText sourceData role label formula annotation kind =>
    let k := '.' :: '\n' :: suffix
    let j := ')' :: k
    let i := sourceText.toList ++ j
    let bodySuffix := ',' :: i
    let g := bodyText.toList ++ ')' :: bodySuffix
    let f := '(' :: g
    let e := ',' :: f
    let d := role.text.toList ++ e
    let c := ',' :: d
    let b := quotedName.toList ++ c
    let a := '(' :: b
    obtain ⟨middle, parsedBody, bodyEnd⟩ :=
      clause_prefix formula bodySuffix (TstpUnique.punctuation_boundary ',' (by decide) i)
    have roleWord : AtomicText role.text role.text := by
      cases role
      · exact checked_lower "axiom" (by decide)
      · exact checked_lower "plain" (by decide)
    refine ⟨a, b, c, d, e, f, g, middle, i, j, k,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, parsedBody, ?_, ?_, ?_, ?_⟩
    · have tag := readToken_atomic (checked_lower "cnf" (by decide)) a
        (TstpUnique.punctuation_boundary '(' (by decide) b)
      simpa [a, b, c, d, e, f, g, bodySuffix, i, j, k,
        String.toList_append, List.append_assoc] using tag
    · exact readToken_punctuation '(' (by decide) b
    · simpa [b] using readToken_quoted label c
    · exact readToken_punctuation ',' (by decide) d
    · exact readToken_atomic roleWord e (TstpUnique.punctuation_boundary ',' (by decide) f)
    · exact readToken_punctuation ',' (by decide) f
    · exact readToken_punctuation '(' (by decide) g
    · exact bodyEnd.trans (readToken_punctuation ',' (by decide) i)
    · exact Fang.TstpUnique.DataText.prefix annotation j (.paren k)
    · exact readToken_punctuation ')' (by decide) k
    · exact readToken_punctuation '.' (by decide) ('\n' :: suffix)

theorem AnnotatedRowText.prefix_unique {left right leftName rightName leftRole rightRole
    leftClause rightClause leftData rightData leftSuffix rightSuffix}
    (first : AnnotatedRowText left leftName leftRole leftClause leftData)
    (second : AnnotatedRowText right rightName rightRole rightClause rightData)
    (same : left.toList ++ leftSuffix = right.toList ++ rightSuffix) :
    leftName = rightName ∧ leftRole = rightRole ∧ leftClause = rightClause ∧
      leftData = rightData ∧ leftSuffix = rightSuffix := by
  have leftParse := first.prefix leftSuffix
  rw [same] at leftParse
  exact leftParse.unique (second.prefix rightSuffix)

theorem AnnotatedRowText.functional {text leftName rightName leftRole rightRole
    leftClause rightClause leftData rightData}
    (first : AnnotatedRowText text leftName leftRole leftClause leftData)
    (second : AnnotatedRowText text rightName rightRole rightClause rightData) :
    leftName = rightName ∧ leftRole = rightRole ∧ leftClause = rightClause ∧ leftData = rightData := by
  obtain ⟨name, role, clause, data, _⟩ :=
    first.prefix_unique (leftSuffix := []) (rightSuffix := []) second rfl
  exact ⟨name, role, clause, data⟩

end Fang.TstpText
