/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Correspondence between classified source tokens and the strings consumed by
the actual parser. These definitions describe token syntax only.
-/
import Fang.FrontendClassification
import Fang.FrontendParser

namespace Fang.Source.Grammar

def Token.text : Token → String
  | .lower name | .variable name => name
  | .lparen => "("
  | .rparen => ")"
  | .comma => ","
  | .period => "."
  | .disjoin => "|"
  | .negate => "~"
  | .falseLiteral => "$false"

end Fang.Source.Grammar

namespace Fang.Frontend

open Source.Grammar

theorem RawTokenSpelling.text {raw : Token} {token : Source.Grammar.Token}
    (classified : RawTokenSpelling raw token) : raw.text = token.text := by
  rcases classified with word | ⟨byte, punctuation, encoded⟩
  · cases word with
    | lower name encoded valid => exact spelling_injective encoded
    | variableWord name encoded valid => exact spelling_injective encoded
    | falsity encoded => exact spelling_injective encoded
  · cases punctuation <;> exact spelling_injective encoded

theorem lowerName_ascii {name : String} (valid : lowerName name = true) :
    ∀ character ∈ name.toList, character.toNat < 128 := by
  cases shape : name.toList with
  | nil => simp [lowerName, shape] at valid
  | cons first rest =>
      simp only [lowerName, shape, Bool.and_eq_true, List.all_eq_true] at valid
      intro character member
      rcases List.mem_cons.mp member with rfl | member
      · have bound := (asciiLower_nat character).mp valid.1
        omega
      · have chosen := valid.2 character member
        simp only [Bool.or_eq_true, beq_iff_eq] at chosen
        rcases chosen with (lower | digit) | same
        · have bound := (asciiLower_nat character).mp lower
          omega
        · have bound := (asciiDigit_nat character).mp digit
          omega
        · subst character
          decide

theorem variableName_ascii {name : String} (valid : variableName name = true) :
    ∀ character ∈ name.toList, character.toNat < 128 := by
  cases shape : name.toList with
  | nil => simp [variableName, shape] at valid
  | cons first rest =>
      simp only [variableName, shape, Bool.and_eq_true, List.all_eq_true] at valid
      intro character member
      rcases List.mem_cons.mp member with rfl | member
      · have bound := (asciiUpper_nat character).mp valid.1
        omega
      · have chosen := valid.2 character member
        simp only [Bool.or_eq_true, beq_iff_eq] at chosen
        rcases chosen with ((lower | upper) | digit) | same
        · have bound := (asciiLower_nat character).mp lower
          omega
        · have bound := (asciiUpper_nat character).mp upper
          omega
        · have bound := (asciiDigit_nat character).mp digit
          omega
        · subst character
          decide

theorem RawTokenSpelling.is_lower {raw : Token} {token : Source.Grammar.Token}
    (classified : RawTokenSpelling raw token) (valid : lowerName raw.text = true) :
    token = .lower raw.text :=
  classified.unique (rawTokenSpelling_lower raw (lowerName_ascii valid) valid)

theorem RawTokenSpelling.is_variable {raw : Token} {token : Source.Grammar.Token}
    (classified : RawTokenSpelling raw token) (valid : variableName raw.text = true) :
    token = .variable raw.text :=
  classified.unique (rawTokenSpelling_variable raw (variableName_ascii valid) valid)

theorem RawTokenSpelling.is_lparen {raw : Token} {token : Source.Grammar.Token}
    (classified : RawTokenSpelling raw token) : raw.text = "(" ↔ token = .lparen := by
  constructor
  · intro text
    exact classified.unique (rawTokenSpelling_punctuation raw '(' (by simp [RawPunctuation]) text .lparen .lparen)
  · intro same
    simpa [same, Source.Grammar.Token.text] using classified.text

theorem RawTokenSpelling.is_rparen {raw : Token} {token : Source.Grammar.Token}
    (classified : RawTokenSpelling raw token) : raw.text = ")" ↔ token = .rparen := by
  constructor
  · intro text
    exact classified.unique (rawTokenSpelling_punctuation raw ')' (by simp [RawPunctuation]) text .rparen .rparen)
  · intro same
    simpa [same, Source.Grammar.Token.text] using classified.text

theorem RawTokenSpelling.is_comma {raw : Token} {token : Source.Grammar.Token}
    (classified : RawTokenSpelling raw token) : raw.text = "," ↔ token = .comma := by
  constructor
  · intro text
    exact classified.unique (rawTokenSpelling_punctuation raw ',' (by simp [RawPunctuation]) text .comma .comma)
  · intro same
    simpa [same, Source.Grammar.Token.text] using classified.text

theorem ClassifiedTokens.head_lparen {raw : List Token} {tokens : List Source.Grammar.Token}
    (classified : ClassifiedTokens raw tokens) :
    raw.head?.map Token.text = some "(" ↔ tokens.head? = some .lparen := by
  cases classified with
  | nil => simp
  | cons head tail => simpa using head.is_lparen

theorem ClassifiedTokens.head_comma {raw : List Token} {tokens : List Source.Grammar.Token}
    (classified : ClassifiedTokens raw tokens) :
    raw.head?.map Token.text = some "," ↔ tokens.head? = some .comma := by
  cases classified with
  | nil => simp
  | cons head tail => simpa using head.is_comma

theorem expect_classified {state updated : State} {wanted : String}
    (success : expect wanted state = .ok ((), updated))
    {tokens : List Source.Grammar.Token} (classified : ClassifiedTokens state.tokens tokens) :
    ∃ token rest, tokens = token :: rest ∧ token.text = wanted ∧
      ClassifiedTokens updated.tokens rest := by
  obtain ⟨raw, raws, shape, text, rfl⟩ := expect_success success
  rw [shape] at classified
  cases classified with
  | cons head tail => exact ⟨_, _, rfl, head.text.symm.trans text, tail⟩

theorem expect_punctuation {state updated : State} {character : Char}
    (success : expect (String.singleton character) state = .ok ((), updated))
    {tokens : List Source.Grammar.Token} (classified : ClassifiedTokens state.tokens tokens)
    (punctuation : RawPunctuation character) (token : Source.Grammar.Token)
    (spelled : Punctuation (asciiByte character) token) :
    ∃ rest, tokens = token :: rest ∧ ClassifiedTokens updated.tokens rest := by
  obtain ⟨raw, raws, shape, text, rfl⟩ := expect_success success
  rw [shape] at classified
  cases classified with
  | cons head tail =>
      have same := head.unique (rawTokenSpelling_punctuation raw character punctuation text token spelled)
      exact ⟨_, congrArg (fun first => first :: _) same, tail⟩

#print axioms RawTokenSpelling.text
#print axioms RawTokenSpelling.is_lower
#print axioms RawTokenSpelling.is_variable
#print axioms expect_classified
#print axioms expect_punctuation

end Fang.Frontend
