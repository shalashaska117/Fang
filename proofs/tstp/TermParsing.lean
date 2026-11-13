/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import VariableNames
import Init.Data.String.Lemmas.Intercalate

namespace Fang.TstpText

open Source.Grammar

theorem spelling_append (left right : String) :
    spelling (left ++ right) = spelling left ++ spelling right := by
  simp [spelling, String.toByteArray_append]

@[simp] theorem spelling_lparen : spelling "(" = [40] := rfl
@[simp] theorem spelling_rparen : spelling ")" = [41] := rfl
@[simp] theorem spelling_comma : spelling "," = [44] := rfl
@[simp] theorem spelling_empty : spelling "" = [] := rfl

def StartsBoundary (bytes : Bytes) : Prop :=
  ∀ byte tail, bytes = byte :: tail → ¬ IsWord byte

theorem punctuation_boundary {byte token rest} (h : Punctuation byte token) :
    StartsBoundary (byte :: rest) := by
  intro other tail equal
  have same := (List.cons.inj equal).1
  subst other
  exact h.not_word

theorem lexeme_append {input middle : Bytes} {token : Token}
    (h : Lexeme input token middle) (suffix : Bytes) (boundary : StartsBoundary suffix) :
    Lexeme (input ++ suffix) token (middle ++ suffix) := by
  cases h with
  | word shape maximal spelled =>
    refine .word (by simp [shape, List.append_assoc]) ⟨maximal.members, ?_⟩ spelled
    intro byte tail equal
    cases hm : middle with
    | nil => exact boundary byte tail (by simpa [hm] using equal)
    | cons first rest =>
      have same : first = byte := (List.cons.inj (by simpa [hm] using equal)).1
      subst byte
      exact maximal.boundary first rest hm
  | punctuation spelled => simpa using Lexeme.punctuation (rest := middle ++ suffix) spelled

theorem tokenization_append {left right : Bytes} {first second : List Token}
    (h₁ : Tokenization left first) (h₂ : Tokenization right second)
    (boundary : StartsBoundary right) :
    Tokenization (left ++ right) (first ++ second) := by
  induction h₁ with
  | empty => simpa using h₂
  | whitespace space _ ih => simpa using Tokenization.whitespace space ih
  | token read _ ih => exact .token (lexeme_append read right boundary) ih

theorem word_tokenization {bytes token} (word : WordSpelling bytes token) :
    Tokenization bytes [token] := by
  apply Tokenization.token (middle := [])
  · exact .word (by simp) ⟨word.word_bytes.2, by intros; contradiction⟩ word
  · exact .empty

mutual
inductive NamedTerm (symbols : List Frontend.Symbol) : Fang.Term → Source.Term → Prop where
  | variable (index : Nat) : NamedTerm symbols (.var index) (.var s!"X{index}")
  | application {index arguments named name}
      (symbol : SymbolText symbols index arguments.length name)
      (children : NamedTerms symbols arguments named) :
      NamedTerm symbols (.app index arguments) (.app name named)
inductive NamedTerms (symbols : List Frontend.Symbol) :
    List Fang.Term → List Source.Term → Prop where
  | nil : NamedTerms symbols [] []
  | cons {first named rest names} (head : NamedTerm symbols first named)
      (tail : NamedTerms symbols rest names) : NamedTerms symbols (first :: rest) (named :: names)
end

def TermBytesParse (bytes : Bytes) (term : Source.Term) : Prop :=
  ∃ tokens, Tokenization bytes tokens ∧ TermTokens tokens term []

theorem TermBytesParse.unique {bytes left right}
    (hl : TermBytesParse bytes left) (hr : TermBytesParse bytes right) : left = right := by
  obtain ⟨tokens, lexical, parsed⟩ := hl
  obtain ⟨other, otherLexical, otherParsed⟩ := hr
  have same := lexical.unique otherLexical
  subst other
  exact (parsed.unique otherParsed).1

mutual
theorem term_tokens {symbols : List Frontend.Symbol} {value : Fang.Term} {text : String}
    (h : TermText symbols value text) :
    ∃ named tokens, NamedTerm symbols value named ∧ Tokenization (spelling text) tokens ∧
      ∀ suffix, suffix.head? ≠ some Token.lparen →
        TermTokens (tokens ++ suffix) named suffix := by
  cases h with
  | «variable» index =>
    refine ⟨.var s!"X{index}", [.variable s!"X{index}"], .variable index,
      word_tokenization (.variableWord _ rfl (variable_name_grammar index)), ?_⟩
    intro suffix _
    exact .variableTerm _ suffix
  | constant symbol =>
    refine ⟨.app _ [], [.lower _], .application symbol .nil,
      word_tokenization (.lower _ rfl symbol.grammar), ?_⟩
    intro suffix boundary
    exact .constant _ suffix boundary
  | @application index arguments rendered name nonempty symbol children =>
    obtain ⟨names, tokens, named, lexical, parsed⟩ := terms_tokens children
    have close : Tokenization ((spelling (String.intercalate "," rendered)) ++ [41])
        (tokens ++ [.rparen]) :=
      tokenization_append lexical (.token (.punctuation .rparen) .empty)
        (punctuation_boundary Punctuation.rparen)
    have openClose := Tokenization.token (Lexeme.punctuation Punctuation.lparen) close
    have whole := tokenization_append (word_tokenization (.lower name rfl symbol.grammar))
      openClose (punctuation_boundary Punctuation.lparen)
    refine ⟨.app name names, .lower name :: .lparen :: (tokens ++ [.rparen]),
      .application symbol named, ?_, ?_⟩
    · simpa [spelling_append, List.append_assoc] using whole
    · intro suffix _
      have body := parsed suffix nonempty
      simpa [List.append_assoc] using TermTokens.application name body
termination_by sizeOf value

theorem terms_tokens {symbols : List Frontend.Symbol} {values : List Fang.Term} {texts : List String}
    (h : TermsText symbols values texts) :
    ∃ names tokens, NamedTerms symbols values names ∧
      Tokenization (spelling (String.intercalate "," texts)) tokens ∧
      ∀ suffix, values ≠ [] →
        ArgumentsTokens (tokens ++ .rparen :: suffix) names suffix := by
  cases h with
  | nil =>
    refine ⟨[], [], .nil, ?_, ?_⟩
    · simpa using Tokenization.empty
    · intros; contradiction
  | @cons first text rest texts head tail =>
    obtain ⟨name, firstTokens, namedHead, lexicalHead, parsedHead⟩ := term_tokens head
    obtain ⟨names, tailTokens, namedTail, lexicalTail, parsedTail⟩ := terms_tokens tail
    cases rest with
    | nil =>
      have len := tail.length
      have empty : texts = [] := by cases texts <;> simp_all
      subst texts
      cases namedTail
      refine ⟨[name], firstTokens, .cons namedHead .nil, ?_, ?_⟩
      · simpa using lexicalHead
      · intro suffix _
        exact .last (parsedHead (.rparen :: suffix) (by simp))
    | cons next remaining =>
      have nonempty : texts ≠ [] := by
        intro empty
        have len := tail.length
        simp [empty] at len
      have commaTail := Tokenization.token (Lexeme.punctuation Punctuation.comma) lexicalTail
      have whole := tokenization_append lexicalHead commaTail
        (punctuation_boundary Punctuation.comma)
      refine ⟨name :: names, firstTokens ++ .comma :: tailTokens,
        .cons namedHead namedTail, ?_, ?_⟩
      · simpa [String.intercalate_cons_of_ne_nil nonempty, spelling_append,
          List.append_assoc] using whole
      · intro suffix _
        have first := parsedHead (.comma :: (tailTokens ++ .rparen :: suffix)) (by simp)
        have rest := parsedTail suffix (by simp)
        simpa [List.append_assoc] using ArgumentsTokens.more first rest
termination_by sizeOf values
end

theorem term_byte_correspondence {symbols : List Frontend.Symbol} (value : Fang.Term)
    {text : String} (accepted : TstpExport.term symbols value = .ok text) :
    ∃ named, NamedTerm symbols value named ∧ TermBytesParse (spelling text) named := by
  obtain ⟨named, tokens, correspondence, lexical, parsed⟩ :=
    term_tokens (term_correspondence value accepted)
  exact ⟨named, correspondence, tokens, lexical, by simpa using parsed [] (by simp)⟩

end Fang.TstpText
