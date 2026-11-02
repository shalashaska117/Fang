/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Token rendering for the independent certificate exporter. This is not a
   verified implementation of a Rust printer or a complete TSTP derivation. -/
import QuantifiedUniqueness

namespace Fang.QuantifiedTstp.Tokens
open NamedQuantified Source.Grammar

def TermNames : Source.Term → Prop
  | .var name => VariableName name
  | .app name arguments => LowerName name ∧ ∀ term ∈ arguments, TermNames term

def FormulaNames : Formula → Prop
  | .atom name arguments => TermNames (.app name arguments)
  | .truth | .falsity => True
  | .neg body => FormulaNames body
  | .conj left right | .disj left right | .implies left right =>
      FormulaNames left ∧ FormulaNames right
  | .all name body | .ex name body => VariableName name ∧ FormulaNames body

mutual
def termTokens : Source.Term → List String
  | .var name => [name]
  | .app name [] => [name]
  | .app name arguments => name :: "(" :: argumentTokens arguments ++ [")"]

def argumentTokens : List Source.Term → List String
  | [] => []
  | [term] => termTokens term
  | term :: rest => termTokens term ++ "," :: argumentTokens rest
end

/-- Atoms have their own parentheses, so a nullary predicate cannot consume a
    following application delimiter. Binder occurrences retain their spelling. -/
def formulaTokens : Formula → List String
  | .atom name arguments => "(" :: termTokens (.app name arguments) ++ [")"]
  | .truth => ["$true"]
  | .falsity => ["$false"]
  | .neg body => "~" :: formulaTokens body
  | .conj left right => "(" :: formulaTokens left ++ "&" :: formulaTokens right ++ [")"]
  | .disj left right => "(" :: formulaTokens left ++ "|" :: formulaTokens right ++ [")"]
  | .implies left right => "(" :: formulaTokens left ++ "=>" :: formulaTokens right ++ [")"]
  | .all name body => "!" :: "[" :: name :: "]" :: ":" :: formulaTokens body
  | .ex name body => "?" :: "[" :: name :: "]" :: ":" :: formulaTokens body

mutual
theorem term_tokens_grammar (term : Source.Term) (valid : TermNames term)
    (suffix : List String) (boundary : suffix.head? ≠ some "(") :
    FOFGrammar.TermTokens (termTokens term ++ suffix) term suffix := by
  cases term with
  | var name =>
    simp only [TermNames] at valid
    simpa only [termTokens, List.singleton_append] using
      FOFGrammar.TermTokens.variableTerm name suffix valid
  | app name arguments =>
    simp only [TermNames] at valid
    cases arguments with
    | nil => exact .constant name suffix valid.1 boundary
    | cons first rest =>
      have child := argument_tokens_grammar (first :: rest) (by simp) valid.2 suffix
      simpa only [termTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
        FOFGrammar.TermTokens.application name valid.1 child
termination_by sizeOf term

theorem argument_tokens_grammar (terms : List Source.Term) (nonempty : terms ≠ [])
    (valid : ∀ term ∈ terms, TermNames term) (suffix : List String) :
    FOFGrammar.ArgumentsTokens (argumentTokens terms ++ ")" :: suffix) terms suffix := by
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
        FOFGrammar.ArgumentsTokens.more head child
termination_by sizeOf terms
end

theorem formula_tokens_grammar (formula : Formula) (valid : FormulaNames formula)
    (suffix : List String) :
    NamedQuantified.Grammar.FormulaTokens (formulaTokens formula ++ suffix) formula suffix := by
  induction formula generalizing suffix with
  | atom name arguments =>
    have atom := term_tokens_grammar (.app name arguments) valid (")" :: suffix) (by simp)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      NamedQuantified.Grammar.FormulaTokens.paren (.atom atom)
  | truth => exact .truth suffix
  | falsity => exact .falsity suffix
  | neg body ih => exact .neg (ih valid suffix)
  | conj left right il ir =>
    have first := il valid.1 ("&" :: (formulaTokens right ++ ")" :: suffix))
    have second := ir valid.2 (")" :: suffix)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      NamedQuantified.Grammar.FormulaTokens.conj first second
  | disj left right il ir =>
    have first := il valid.1 ("|" :: (formulaTokens right ++ ")" :: suffix))
    have second := ir valid.2 (")" :: suffix)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      NamedQuantified.Grammar.FormulaTokens.disj first second
  | implies left right il ir =>
    have first := il valid.1 ("=>" :: (formulaTokens right ++ ")" :: suffix))
    have second := ir valid.2 (")" :: suffix)
    simpa only [formulaTokens, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
      NamedQuantified.Grammar.FormulaTokens.implies first second
  | all name body ih =>
    have parsed := NamedQuantified.Grammar.FormulaTokens.all
      (NamedQuantified.Grammar.BindersTokens.last (rest := ":" :: (formulaTokens body ++ suffix)) valid.1)
      (ih valid.2 suffix)
    simpa [formulaTokens, NamedQuantified.Formula.bind] using parsed
  | ex name body ih =>
    have parsed := NamedQuantified.Grammar.FormulaTokens.ex
      (NamedQuantified.Grammar.BindersTokens.last (rest := ":" :: (formulaTokens body ++ suffix)) valid.1)
      (ih valid.2 suffix)
    simpa [formulaTokens, NamedQuantified.Formula.bind] using parsed

theorem formula_tokens_unique {formula other : Formula} (valid : FormulaNames formula)
    {suffix otherSuffix : List String}
    (parsed : NamedQuantified.Grammar.FormulaTokens (formulaTokens formula ++ suffix) other otherSuffix) :
    formula = other ∧ suffix = otherSuffix :=
  (formula_tokens_grammar formula valid suffix).unique parsed

theorem empty_predicate_control : formulaTokens (.atom "p" []) = ["(", "p", ")"] := rfl
theorem nested_term_control : termTokens (.app "f" [.var "X", .app "a" []]) =
    ["f", "(", "X", ",", "a", ")"] := rfl
theorem shadowed_binder_control : formulaTokens (.all "X" (.ex "X" (.atom "p" [.var "X"]))) =
    ["!", "[", "X", "]", ":", "?", "[", "X", "]", ":", "(", "p", "(", "X", ")", ")"] := rfl
theorem binary_scope_control : formulaTokens (.conj (.all "X" .truth) (.ex "X" .falsity)) =
    ["(", "!", "[", "X", "]", ":", "$true", "&", "?", "[", "X", "]", ":", "$false", ")"] := rfl

#print axioms Fang.QuantifiedTstp.Tokens.term_tokens_grammar
#print axioms Fang.QuantifiedTstp.Tokens.argument_tokens_grammar
#print axioms Fang.QuantifiedTstp.Tokens.formula_tokens_grammar
#print axioms Fang.QuantifiedTstp.Tokens.formula_tokens_unique
#print axioms Fang.QuantifiedTstp.Tokens.empty_predicate_control
#print axioms Fang.QuantifiedTstp.Tokens.nested_term_control
#print axioms Fang.QuantifiedTstp.Tokens.shadowed_binder_control
#print axioms Fang.QuantifiedTstp.Tokens.binary_scope_control

end Fang.QuantifiedTstp.Tokens
