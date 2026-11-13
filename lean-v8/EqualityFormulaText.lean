/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Token and byte rendering of version-7 named formulas for the certificate
   exporter. Adapted from the accepted equality-free QuantifiedTokens and
   QuantifiedBytes pair; equality atoms are added. Names print as TPTP atomic
   words: a lower word as it is, any other name as a single-quoted atom. The
   text reads back under the formula lexemes and grammar of
   `EqualityFormulaLexing` and `EqualityFormulaGrammar`, which extend the
   version-7 ones with those words. Formula name validity is an explicit caller
   obligation. -/
import EqualityFormulaLexing
import EqualityFormulaGrammar

namespace Fang.QuantifiedEqualityTstp.FormulaText
open NamedQuantifiedEquality Source.Grammar

def TermNames : Source.Term → Prop
  | .var binder => VariableName binder
  | .app symbol arguments => TstpText.PrintableName symbol ∧ ∀ term ∈ arguments, TermNames term

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
  | .app symbol [] => [TstpExport.symbolText symbol]
  | .app symbol arguments => TstpExport.symbolText symbol :: "(" :: argumentTokens arguments ++ [")"]

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
    FormulaGrammar.TermTokens (termTokens term ++ suffix) term suffix := by
  cases term with
  | var binder =>
    simp only [TermNames] at valid
    simpa only [termTokens, List.singleton_append] using
      FormulaGrammar.TermTokens.variableTerm binder suffix valid
  | app symbol arguments =>
    simp only [TermNames] at valid
    cases arguments with
    | nil => exact .constant suffix (TstpText.symbolText_atomic valid.1) boundary
    | cons first rest =>
      have child := argument_tokens_grammar (first :: rest) (by simp) valid.2 suffix
      simpa only [termTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
        FormulaGrammar.TermTokens.application (TstpText.symbolText_atomic valid.1) child
termination_by sizeOf term

theorem argument_tokens_grammar (terms : List Source.Term) (nonempty : terms ≠ [])
    (valid : ∀ term ∈ terms, TermNames term) (suffix : List String) :
    FormulaGrammar.ArgumentsTokens (argumentTokens terms ++ ")" :: suffix) terms suffix := by
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
        FormulaGrammar.ArgumentsTokens.more head child
termination_by sizeOf terms
end

theorem atom_tokens_grammar (value : NamedQuantifiedEquality.Atom) (valid : AtomNames value) (suffix : List String) :
    FormulaGrammar.AtomTokens (atomTokens value ++ ")" :: suffix) (.atom value) (")" :: suffix) := by
  cases value with
  | predicate symbol arguments =>
    exact .predicate (term_tokens_grammar (.app symbol arguments) valid (")" :: suffix) (by simp))
      (by simp [EqualitySource.Grammar.PredicateEnd])
  | equal left right =>
    have first := term_tokens_grammar left valid.1 ("=" :: (termTokens right ++ ")" :: suffix)) (by simp)
    have second := term_tokens_grammar right valid.2 (")" :: suffix) (by simp)
    simpa only [atomTokens, List.cons_append, List.append_assoc] using FormulaGrammar.AtomTokens.equal first second

theorem formula_tokens_grammar (formula : Formula) (valid : FormulaNames formula)
    (suffix : List String) :
    FormulaGrammar.FormulaTokens (formulaTokens formula ++ suffix) formula suffix := by
  induction formula generalizing suffix with
  | atom value =>
    have atom := atom_tokens_grammar value valid suffix
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      FormulaGrammar.FormulaTokens.paren (.atom atom)
  | truth => exact .truth suffix
  | falsity => exact .falsity suffix
  | neg body ih => exact .neg (ih valid suffix)
  | conj left right il ir =>
    have first := il valid.1 ("&" :: (formulaTokens right ++ ")" :: suffix))
    have second := ir valid.2 (")" :: suffix)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      FormulaGrammar.FormulaTokens.conj first second
  | disj left right il ir =>
    have first := il valid.1 ("|" :: (formulaTokens right ++ ")" :: suffix))
    have second := ir valid.2 (")" :: suffix)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      FormulaGrammar.FormulaTokens.disj first second
  | implies left right il ir =>
    have first := il valid.1 ("=>" :: (formulaTokens right ++ ")" :: suffix))
    have second := ir valid.2 (")" :: suffix)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      FormulaGrammar.FormulaTokens.implies first second
  | all binder body ih =>
    have parsed := FormulaGrammar.FormulaTokens.all
      (NamedQuantifiedEquality.Grammar.BindersTokens.last (rest := ":" :: (formulaTokens body ++ suffix)) valid.1)
      (ih valid.2 suffix)
    simpa [formulaTokens, Formula.bind] using parsed
  | ex binder body ih =>
    have parsed := FormulaGrammar.FormulaTokens.ex
      (NamedQuantifiedEquality.Grammar.BindersTokens.last (rest := ":" :: (formulaTokens body ++ suffix)) valid.1)
      (ih valid.2 suffix)
    simpa [formulaTokens, Formula.bind] using parsed

theorem formula_tokens_unique {formula other : Formula} (valid : FormulaNames formula)
    {suffix otherSuffix : List String}
    (parsed : FormulaGrammar.FormulaTokens (formulaTokens formula ++ suffix) other otherSuffix) :
    formula = other ∧ suffix = otherSuffix :=
  (formula_tokens_grammar formula valid suffix).unique parsed

mutual
theorem term_tokens_standalone (term : Source.Term) (valid : TermNames term) :
    ∀ token ∈ termTokens term, FormulaLexing.Standalone token := by
  cases term with
  | var binder =>
    simp only [TermNames] at valid
    simpa [termTokens] using FormulaLexing.standalone_variable valid
  | app symbol arguments =>
    simp only [TermNames] at valid
    have name := FormulaLexing.standalone_atomic (TstpText.symbolText_atomic valid.1)
    cases arguments with
    | nil => simpa [termTokens] using name
    | cons first rest =>
      have children := argument_tokens_standalone (first :: rest) valid.2
      simp only [termTokens, List.forall_mem_cons, List.forall_mem_append,
        and_assoc]
      exact ⟨name, FormulaLexing.standalone_open, children, FormulaLexing.standalone_close, by simp⟩
termination_by sizeOf term

theorem argument_tokens_standalone (terms : List Source.Term) (valid : ∀ term ∈ terms, TermNames term) :
    ∀ token ∈ argumentTokens terms, FormulaLexing.Standalone token := by
  cases terms with
  | nil => simp [argumentTokens]
  | cons first rest =>
    have head := term_tokens_standalone first (valid first (by simp))
    cases rest with
    | nil => simpa [argumentTokens] using head
    | cons second tail =>
      have more := argument_tokens_standalone (second :: tail) (fun term member => valid term (by simp [member]))
      simp only [argumentTokens, List.forall_mem_cons, List.forall_mem_append]
      exact ⟨head, FormulaLexing.standalone_comma, more⟩
termination_by sizeOf terms
end

theorem formula_tokens_standalone (formula : Formula) (valid : FormulaNames formula) :
    ∀ token ∈ formulaTokens formula, FormulaLexing.Standalone token := by
  induction formula with
  | atom value =>
    cases value with
    | predicate symbol arguments =>
      have inner := term_tokens_standalone (.app symbol arguments) valid
      simp only [formulaTokens, atomTokens, List.forall_mem_cons, List.forall_mem_append,
        and_assoc]
      exact ⟨FormulaLexing.standalone_open, inner, FormulaLexing.standalone_close, by simp⟩
    | equal left right =>
      have one := term_tokens_standalone left valid.1
      have two := term_tokens_standalone right valid.2
      simp only [formulaTokens, atomTokens, List.forall_mem_cons, List.forall_mem_append,
        and_assoc]
      exact ⟨FormulaLexing.standalone_open, one, FormulaLexing.standalone_equal, two,
        FormulaLexing.standalone_close, by simp⟩
  | truth => simpa [formulaTokens] using FormulaLexing.standalone_truth
  | falsity => simpa [formulaTokens] using FormulaLexing.standalone_falsity
  | neg body ih =>
    simp only [formulaTokens, List.forall_mem_cons]
    exact ⟨FormulaLexing.standalone_not, ih valid⟩
  | conj left right il ir =>
    simp only [formulaTokens, List.forall_mem_cons, List.forall_mem_append,
      and_assoc]
    exact ⟨FormulaLexing.standalone_open, il valid.1, FormulaLexing.standalone_and, ir valid.2,
      FormulaLexing.standalone_close, by simp⟩
  | disj left right il ir =>
    simp only [formulaTokens, List.forall_mem_cons, List.forall_mem_append,
      and_assoc]
    exact ⟨FormulaLexing.standalone_open, il valid.1, FormulaLexing.standalone_or, ir valid.2,
      FormulaLexing.standalone_close, by simp⟩
  | implies left right il ir =>
    simp only [formulaTokens, List.forall_mem_cons, List.forall_mem_append,
      and_assoc]
    exact ⟨FormulaLexing.standalone_open, il valid.1, FormulaLexing.standalone_implication, ir valid.2,
      FormulaLexing.standalone_close, by simp⟩
  | all binder body ih =>
    simp only [formulaTokens, List.forall_mem_cons]
    exact ⟨FormulaLexing.standalone_all, FormulaLexing.standalone_lbracket,
      FormulaLexing.standalone_variable valid.1, FormulaLexing.standalone_rbracket,
      FormulaLexing.standalone_colon, ih valid.2⟩
  | ex binder body ih =>
    simp only [formulaTokens, List.forall_mem_cons]
    exact ⟨FormulaLexing.standalone_ex, FormulaLexing.standalone_lbracket,
      FormulaLexing.standalone_variable valid.1, FormulaLexing.standalone_rbracket,
      FormulaLexing.standalone_colon, ih valid.2⟩

/-- The tokens separated by single spaces. Every name is printed as an atomic
    word, so the text reads back as exactly these tokens. -/
def render (formula : Formula) : Except String String :=
  .ok (String.intercalate " " (formulaTokens formula))

/-- A complete formula, without a declaration wrapper or remaining tokens. -/
def ParsesFormula (bytes : List UInt8) (formula : Formula) : Prop :=
  ∃ tokens, FormulaLexing.FormulaByteTokenization bytes tokens ∧
    FormulaGrammar.FormulaTokens tokens formula []

theorem render_formula {formula returned}
    (valid : FormulaNames formula) (success : render formula = .ok returned) :
    ParsesFormula (spelling returned) formula := by
  simp only [render, Except.ok.injEq] at success
  subst returned
  have lexical := FormulaLexing.intercalate_tokenization (formulaTokens formula)
    (formula_tokens_standalone formula valid)
  refine ⟨formulaTokens formula, ⟨_, lexical, ?_⟩, ?_⟩
  · exact (spelling_ascii _ lexical.ascii).symm
  · simpa using formula_tokens_grammar formula valid []

theorem ParsesFormula.unique {bytes left right}
    (first : ParsesFormula bytes left) (second : ParsesFormula bytes right) : left = right := by
  obtain ⟨firstTokens, firstLex, firstGrammar⟩ := first
  obtain ⟨secondTokens, secondLex, secondGrammar⟩ := second
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
theorem lower_word_control :
    render (.atom (.predicate "aNaturalNumber0" [.app "xP" []])) = .ok "( aNaturalNumber0 ( xP ) )" := rfl
theorem quoted_control :
    render (.atom (.equal (.app "E" [.var "X0"]) (.app "0" []))) = .ok "( 'E' ( X0 ) = '0' )" := rfl
theorem escape_control :
    render (.atom (.predicate "it's" [])) = .ok "( 'it\\'s' )" := rfl

#print axioms Fang.QuantifiedEqualityTstp.FormulaText.term_tokens_grammar
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.argument_tokens_grammar
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.atom_tokens_grammar
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.formula_tokens_grammar
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.formula_tokens_unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.formula_tokens_standalone
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.render_formula
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.ParsesFormula.unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.render_unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.equality_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.disequality_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.nullary_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.closure_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.lower_word_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.quoted_control
#print axioms Fang.QuantifiedEqualityTstp.FormulaText.escape_control

end Fang.QuantifiedEqualityTstp.FormulaText
