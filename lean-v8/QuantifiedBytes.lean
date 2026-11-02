/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Checked text emission for the independent Lean certificate exporter.
   Formula name validity is an explicit caller obligation. -/
import QuantifiedTokens
import QuantifiedByteGrammar

namespace Fang.QuantifiedTstp.Bytes
open NamedQuantified Source.Grammar

/-- Check the exact text returned to the caller with the accepted lexer. -/
def checkedText (expected : List String) (text : String) : Except String String := do
  let raw ← QuantifiedFrontend.tokenize text
  if raw.map Frontend.Token.text == expected then
    pure text
  else
    .error "export-error: printed tokens differ from the formula"

def render (formula : Formula) : Except String String :=
  checkedText (Tokens.formulaTokens formula)
    (String.intercalate " " (Tokens.formulaTokens formula))

/-- A complete formula, without a declaration wrapper or remaining tokens. -/
def ParsesFormula (bytes : List UInt8) (formula : Formula) : Prop :=
  ∃ raw, QuantifiedFrontend.QuantifiedByteTokenization bytes 0 raw ∧
    NamedQuantified.Grammar.FormulaTokens (raw.map Frontend.Token.text) formula []

theorem checkedText_exact {expected text returned}
    (success : checkedText expected text = .ok returned) :
    returned = text ∧ ∃ raw, QuantifiedFrontend.tokenize returned = .ok raw ∧
      raw.map Frontend.Token.text = expected := by
  cases lexed : QuantifiedFrontend.tokenize text with
  | error error => simp [checkedText, lexed, bind, Except.bind] at success
  | ok raw =>
    by_cases equal : raw.map Frontend.Token.text = expected
    · simp [checkedText, lexed, equal, bind, Except.bind, pure, Except.pure] at success
      subst returned
      exact ⟨rfl, raw, lexed, equal⟩
    · simp [checkedText, lexed, equal, bind, Except.bind] at success

theorem checkedText_formula {formula text returned}
    (valid : Tokens.FormulaNames formula)
    (success : checkedText (Tokens.formulaTokens formula) text = .ok returned) :
    ParsesFormula (spelling returned) formula := by
  obtain ⟨_, raw, lexed, same⟩ := checkedText_exact success
  refine ⟨raw, (QuantifiedFrontend.quantified_tokenize_bytes_iff returned raw).mp lexed, ?_⟩
  rw [same]
  simpa using Tokens.formula_tokens_grammar formula valid []

theorem render_formula {formula returned}
    (valid : Tokens.FormulaNames formula) (success : render formula = .ok returned) :
    ParsesFormula (spelling returned) formula :=
  checkedText_formula valid success

theorem ParsesFormula.unique {bytes left right}
    (first : ParsesFormula bytes left) (second : ParsesFormula bytes right) : left = right := by
  obtain ⟨firstRaw, firstLex, firstGrammar⟩ := first
  obtain ⟨secondRaw, secondLex, secondGrammar⟩ := second
  obtain rfl := firstLex.unique secondLex
  exact (firstGrammar.unique secondGrammar).1

theorem render_unique {formula returned other}
    (valid : Tokens.FormulaNames formula) (success : render formula = .ok returned)
    (otherParse : ParsesFormula (spelling returned) other) : formula = other :=
  (render_formula valid success).unique otherParse

theorem truth_control : render .truth = .ok "$true" := rfl
theorem nullary_control : render (.atom "p" []) = .ok "( p )" := rfl
theorem shadow_control : render (.all "X" (.ex "X" (.atom "p" [.var "X"]))) =
    .ok "! [ X ] : ? [ X ] : ( p ( X ) )" := rfl
theorem scope_control : render (.conj (.all "X" .truth) (.ex "X" .falsity)) =
    .ok "( ! [ X ] : $true & ? [ X ] : $false )" := rfl

theorem altered_quantifier_rejected :
    (checkedText (Tokens.formulaTokens (.all "X" (.atom "p" [.var "X"])))
      "? [ X ] : ( p ( X ) )").isOk = false := rfl
theorem extra_token_rejected :
    (checkedText (Tokens.formulaTokens (.atom "p" [])) "( p ) q").isOk = false := rfl
theorem nonascii_rejected : (checkedText ["p"] "pλ").isOk = false := rfl

#print axioms Fang.QuantifiedTstp.Bytes.checkedText_exact
#print axioms Fang.QuantifiedTstp.Bytes.checkedText_formula
#print axioms Fang.QuantifiedTstp.Bytes.render_formula
#print axioms Fang.QuantifiedTstp.Bytes.ParsesFormula.unique
#print axioms Fang.QuantifiedTstp.Bytes.render_unique
#print axioms Fang.QuantifiedTstp.Bytes.truth_control
#print axioms Fang.QuantifiedTstp.Bytes.nullary_control
#print axioms Fang.QuantifiedTstp.Bytes.shadow_control
#print axioms Fang.QuantifiedTstp.Bytes.scope_control
#print axioms Fang.QuantifiedTstp.Bytes.altered_quantifier_rejected
#print axioms Fang.QuantifiedTstp.Bytes.extra_token_rejected
#print axioms Fang.QuantifiedTstp.Bytes.nonascii_rejected

end Fang.QuantifiedTstp.Bytes
