/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Token and byte rendering of version-7 named formulas for the certificate
   exporter. Adapted from the accepted equality-free QuantifiedTokens and
   QuantifiedBytes pair; equality atoms are added and the version-7 lexer and
   grammar are used. Formula name validity is an explicit caller obligation. -/
import EqualityQuantifiedUniqueness
import EqualityQuantifiedLexing

namespace Fang.QuantifiedEqualityTstp.FormulaText
open NamedQuantifiedEquality Source.Grammar

def TermNames : Source.Term → Prop
  | .var binder => VariableName binder
  | .app symbol arguments => LowerName symbol ∧ ∀ term ∈ arguments, TermNames term

def AtomNames : NamedQuantifiedEquality.Atom → Prop
  | .predicate symbol arguments => TermNames (.app symbol arguments)
  | .equal left right => TermNames left ∧ TermNames right

def FormulaNames : NamedQuantifiedEquality.Formula → Prop
  | .atom value => AtomNames value
  | .truth | .falsity => True
  | .neg body => FormulaNames body
  | .conj left right | .disj left right | .implies left right =>
      FormulaNames left ∧ FormulaNames right
  | .all binder body | .ex binder body => VariableName binder ∧ FormulaNames body

mutual
def termTokens : Source.Term → List String
  | .var binder => [binder]
  | .app symbol [] => [symbol]
  | .app symbol arguments => symbol :: "(" :: argumentTokens arguments ++ [")"]

def argumentTokens : List Source.Term → List String
  | [] => []
  | [term] => termTokens term
  | term :: rest => termTokens term ++ "," :: argumentTokens rest
end

def atomTokens : NamedQuantifiedEquality.Atom → List String
  | .predicate symbol arguments => termTokens (.app symbol arguments)
  | .equal left right => termTokens left ++ "=" :: termTokens right

/-- Atoms have their own parentheses, so a nullary predicate cannot consume a
    following application delimiter and an equality cannot absorb a connective. -/
def formulaTokens : NamedQuantifiedEquality.Formula → List String
  | .atom value => "(" :: atomTokens value ++ [")"]
  | .truth => ["$true"]
  | .falsity => ["$false"]
  | .neg body => "~" :: formulaTokens body
  | .conj left right => "(" :: formulaTokens left ++ "&" :: formulaTokens right ++ [")"]
  | .disj left right => "(" :: formulaTokens left ++ "|" :: formulaTokens right ++ [")"]
  | .implies left right => "(" :: formulaTokens left ++ "=>" :: formulaTokens right ++ [")"]
  | .all binder body => "!" :: "[" :: binder :: "]" :: ":" :: formulaTokens body
  | .ex binder body => "?" :: "[" :: binder :: "]" :: ":" :: formulaTokens body

mutual
theorem term_tokens_grammar (term : Source.Term) (valid : TermNames term)
    (suffix : List String) (boundary : suffix.head? ≠ some "(") :
    EqualitySource.Grammar.TermTokens (termTokens term ++ suffix) term suffix := by
  cases term with
  | var binder =>
    simp only [TermNames] at valid
    simpa only [termTokens, List.singleton_append] using
      EqualitySource.Grammar.TermTokens.variableTerm binder suffix valid
  | app symbol arguments =>
    simp only [TermNames] at valid
    cases arguments with
    | nil => exact .constant symbol suffix valid.1 boundary
    | cons first rest =>
      have child := argument_tokens_grammar (first :: rest) (by simp) valid.2 suffix
      simpa only [termTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
        EqualitySource.Grammar.TermTokens.application symbol valid.1 child
termination_by sizeOf term

theorem argument_tokens_grammar (terms : List Source.Term) (nonempty : terms ≠ [])
    (valid : ∀ term ∈ terms, TermNames term) (suffix : List String) :
    EqualitySource.Grammar.ArgumentsTokens (argumentTokens terms ++ ")" :: suffix) terms suffix := by
  cases terms with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    cases rest with
    | nil =>
      exact .last (term_tokens_grammar first (valid first (by simp)) (")" :: suffix) (by simp))
    | cons second tail =>
      have child := argument_tokens_grammar (second :: tail) (by simp)
        (fun term member => valid term (by simp [member])) suffix
      have head := term_tokens_grammar first (valid first (by simp))
        ("," :: (argumentTokens (second :: tail) ++ ")" :: suffix)) (by simp)
      simpa only [argumentTokens, List.append_assoc, List.cons_append] using
        EqualitySource.Grammar.ArgumentsTokens.more head child
termination_by sizeOf terms
end

theorem atom_tokens_grammar (value : NamedQuantifiedEquality.Atom) (valid : AtomNames value) (suffix : List String) :
    Grammar.AtomTokens (atomTokens value ++ ")" :: suffix) (.atom value) (")" :: suffix) := by
  cases value with
  | predicate symbol arguments =>
    exact .predicate (term_tokens_grammar (.app symbol arguments) valid (")" :: suffix) (by simp))
      (by simp [EqualitySource.Grammar.PredicateEnd])
  | equal left right =>
    have first := term_tokens_grammar left valid.1 ("=" :: (termTokens right ++ ")" :: suffix)) (by simp)
    have second := term_tokens_grammar right valid.2 (")" :: suffix) (by simp)
    simpa only [atomTokens, List.cons_append, List.append_assoc] using Grammar.AtomTokens.equal first second

theorem formula_tokens_grammar (formula : Formula) (valid : FormulaNames formula)
    (suffix : List String) :
    Grammar.FormulaTokens (formulaTokens formula ++ suffix) formula suffix := by
  induction formula generalizing suffix with
  | atom value =>
    have atom := atom_tokens_grammar value valid suffix
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      Grammar.FormulaTokens.paren (.atom atom)
  | truth => exact .truth suffix
  | falsity => exact .falsity suffix
  | neg body ih => exact .neg (ih valid suffix)
  | conj left right il ir =>
    have first := il valid.1 ("&" :: (formulaTokens right ++ ")" :: suffix))
    have second := ir valid.2 (")" :: suffix)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      Grammar.FormulaTokens.conj first second
  | disj left right il ir =>
    have first := il valid.1 ("|" :: (formulaTokens right ++ ")" :: suffix))
    have second := ir valid.2 (")" :: suffix)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      Grammar.FormulaTokens.disj first second
  | implies left right il ir =>
    have first := il valid.1 ("=>" :: (formulaTokens right ++ ")" :: suffix))
    have second := ir valid.2 (")" :: suffix)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      Grammar.FormulaTokens.implies first second
  | all binder body ih =>
    have parsed := Grammar.FormulaTokens.all
      (Grammar.BindersTokens.last (rest := ":" :: (formulaTokens body ++ suffix)) valid.1)
      (ih valid.2 suffix)
    simpa [formulaTokens, Formula.bind] using parsed
  | ex binder body ih =>
    have parsed := Grammar.FormulaTokens.ex
      (Grammar.BindersTokens.last (rest := ":" :: (formulaTokens body ++ suffix)) valid.1)
      (ih valid.2 suffix)
    simpa [formulaTokens, Formula.bind] using parsed

theorem formula_tokens_unique {formula other : Formula} (valid : FormulaNames formula)
    {suffix otherSuffix : List String}
    (parsed : Grammar.FormulaTokens (formulaTokens formula ++ suffix) other otherSuffix) :
    formula = other ∧ suffix = otherSuffix :=
  (formula_tokens_grammar formula valid suffix).unique parsed

/-- Check the exact text returned to the caller with the accepted version-7 lexer. -/
def checkedText (expected : List String) (text : String) : Except String String := do
  let raw ← QuantifiedEqualityFrontend.tokenize text
  if raw.map Frontend.Token.text == expected then
    pure text
  else
    .error "export-error: printed tokens differ from the formula"

def render (formula : Formula) : Except String String :=
  checkedText (formulaTokens formula) (String.intercalate " " (formulaTokens formula))

/-- A complete formula, without a declaration wrapper or remaining tokens. -/
def ParsesFormula (bytes : List UInt8) (formula : Formula) : Prop :=
  ∃ raw, QuantifiedEqualityFrontend.QuantifiedEqualityByteTokenization bytes 0 raw ∧
    Grammar.FormulaTokens (raw.map Frontend.Token.text) formula []

theorem checkedText_exact {expected text returned}
    (success : checkedText expected text = .ok returned) :
    returned = text ∧ ∃ raw, QuantifiedEqualityFrontend.tokenize returned = .ok raw ∧
      raw.map Frontend.Token.text = expected := by
  cases lexed : QuantifiedEqualityFrontend.tokenize text with
  | error error => simp [checkedText, lexed, bind, Except.bind] at success
  | ok raw =>
    by_cases equal : raw.map Frontend.Token.text = expected
    · simp [checkedText, lexed, equal, bind, Except.bind, pure, Except.pure] at success
      subst returned
      exact ⟨rfl, raw, lexed, equal⟩
    · simp [checkedText, lexed, equal, bind, Except.bind] at success

theorem checkedText_formula {formula text returned}
    (valid : FormulaNames formula)
    (success : checkedText (formulaTokens formula) text = .ok returned) :
    ParsesFormula (spelling returned) formula := by
  obtain ⟨_, raw, lexed, same⟩ := checkedText_exact success
  refine ⟨raw, (QuantifiedEqualityFrontend.tokenize_bytes_iff returned raw).mp lexed, ?_⟩
  rw [same]
  simpa using formula_tokens_grammar formula valid []

theorem render_formula {formula returned}
    (valid : FormulaNames formula) (success : render formula = .ok returned) :
    ParsesFormula (spelling returned) formula :=
  checkedText_formula valid success

theorem ParsesFormula.unique {bytes left right}
    (first : ParsesFormula bytes left) (second : ParsesFormula bytes right) : left = right := by
  obtain ⟨firstRaw, firstLex, firstGrammar⟩ := first
  obtain ⟨secondRaw, secondLex, secondGrammar⟩ := second
  obtain rfl := firstLex.unique secondLex
  exact (firstGrammar.unique secondGrammar).1

theorem render_unique {formula returned other}
    (valid : FormulaNames formula) (success : render formula = .ok returned)
    (otherParse : ParsesFormula (spelling returned) other) : formula = other :=
  (render_formula valid success).unique otherParse

theorem equality_control :
    render (.atom (.equal (.var "X0") (.app "a" []))) = .ok "( X0 = a )" := rfl
theorem disequality_control :
    render (.neg (.atom (.equal (.app "f" [.var "X0"]) (.app "a" [])))) =
      .ok "~ ( f ( X0 ) = a )" := rfl
theorem nullary_control : render (.atom (.predicate "p" [])) = .ok "( p )" := rfl
theorem closure_control :
    render (.all "X0" (.disj (.atom (.predicate "p" [.var "X0"])) (.atom (.equal (.var "X0") (.app "a" []))))) =
      .ok "! [ X0 ] : ( ( p ( X0 ) ) | ( X0 = a ) )" := rfl
theorem altered_operator_rejected :
    (checkedText (formulaTokens (.atom (.equal (.var "X0") (.app "a" [])))) "( X0 != a )").isOk = false := rfl
theorem extra_token_rejected :
    (checkedText (formulaTokens (.atom (.predicate "p" []))) "( p ) q").isOk = false := rfl
theorem nonascii_rejected : (checkedText ["p"] "pλ").isOk = false := rfl

#print axioms Fang.QuantifiedEqualityTstp.FormulaText.term_tokens_grammar
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.argument_tokens_grammar
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.atom_tokens_grammar
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.formula_tokens_grammar
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.formula_tokens_unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.checkedText_exact
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.checkedText_formula
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.render_formula
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.ParsesFormula.unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.render_unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.equality_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.disequality_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.nullary_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.closure_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.altered_operator_rejected
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.extra_token_rejected
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.nonascii_rejected

end Fang.QuantifiedEqualityTstp.FormulaText
