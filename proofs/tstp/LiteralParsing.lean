/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import TermParsing

namespace Fang.TstpText

open Source.Grammar

@[simp] theorem spelling_negate : spelling "~" = [126] := rfl

structure NamedLiteral (problem : TstpExport.NamedProblem) (value : Fang.Literal)
    (named : Source.Literal) : Prop where
  polarity : named.positive = value.positive
  predicate : SymbolText problem.predicates value.atom.pred value.atom.args.length named.predicate
  arguments : NamedTerms problem.functions value.atom.args named.arguments

def LiteralBytesParse (bytes : Bytes) (literal : Source.Literal) : Prop :=
  ∃ tokens, Tokenization bytes tokens ∧ LiteralTokens tokens literal []

theorem LiteralBytesParse.unique {bytes left right}
    (hl : LiteralBytesParse bytes left) (hr : LiteralBytesParse bytes right) : left = right := by
  obtain ⟨tokens, lexical, parsed⟩ := hl
  obtain ⟨other, otherLexical, otherParsed⟩ := hr
  have same := lexical.unique otherLexical
  subst other
  exact (parsed.unique otherParsed).1

theorem atom_tokens {problem : TstpExport.NamedProblem} {value : Fang.Atom} {text : String}
    (h : AtomText problem value text) :
    ∃ name names tokens,
      SymbolText problem.predicates value.pred value.args.length name ∧
      NamedTerms problem.functions value.args names ∧ Tokenization (spelling text) tokens ∧
      ∀ suffix, suffix.head? ≠ some Token.lparen →
        TermTokens (tokens ++ suffix) (.app name names) suffix := by
  cases h with
  | nullary symbol =>
    refine ⟨_, [], [.lower _], symbol, .nil,
      word_tokenization (.lower _ rfl symbol.grammar), ?_⟩
    intro suffix boundary
    exact .constant _ suffix boundary
  | @application predicate arguments rendered name nonempty symbol children =>
    obtain ⟨names, tokens, named, lexical, parsed⟩ := terms_tokens children
    have close : Tokenization ((spelling (String.intercalate "," rendered)) ++ [41])
        (tokens ++ [.rparen]) :=
      tokenization_append lexical (.token (.punctuation .rparen) .empty)
        (punctuation_boundary Punctuation.rparen)
    have openClose := Tokenization.token (Lexeme.punctuation Punctuation.lparen) close
    have whole := tokenization_append (word_tokenization (.lower name rfl symbol.grammar))
      openClose (punctuation_boundary Punctuation.lparen)
    refine ⟨name, names, .lower name :: .lparen :: (tokens ++ [.rparen]),
      symbol, named, ?_, ?_⟩
    · simpa [spelling_append, List.append_assoc] using whole
    · intro suffix _
      have body := parsed suffix nonempty
      simpa [List.append_assoc] using TermTokens.application name body

theorem literal_tokens {problem : TstpExport.NamedProblem} {value : Fang.Literal} {text : String}
    (h : LiteralText problem value text) :
    ∃ named tokens, NamedLiteral problem value named ∧ Tokenization (spelling text) tokens ∧
      ∀ suffix, suffix.head? ≠ some Token.lparen →
        LiteralTokens (tokens ++ suffix) named suffix := by
  cases h with
  | positive body =>
    obtain ⟨name, names, tokens, symbol, named, lexical, parsed⟩ := atom_tokens body
    refine ⟨⟨true, name, names⟩, tokens, ⟨rfl, symbol, named⟩, lexical, ?_⟩
    intro suffix boundary
    exact .positive (parsed suffix boundary)
  | negative body =>
    obtain ⟨name, names, tokens, symbol, named, lexical, parsed⟩ := atom_tokens body
    refine ⟨⟨false, name, names⟩, .negate :: tokens, ⟨rfl, symbol, named⟩, ?_, ?_⟩
    · simpa [spelling_append] using
        Tokenization.token (Lexeme.punctuation Punctuation.negate) lexical
    · intro suffix boundary
      exact .negative (parsed suffix boundary)

theorem literal_byte_correspondence {problem : TstpExport.NamedProblem} (value : Fang.Literal)
    {text : String} (accepted : TstpExport.literal problem value = .ok text) :
    ∃ named, NamedLiteral problem value named ∧ LiteralBytesParse (spelling text) named := by
  obtain ⟨named, tokens, correspondence, lexical, parsed⟩ :=
    literal_tokens (literal_correspondence value accepted)
  exact ⟨named, correspondence, tokens, lexical, by simpa using parsed [] (by simp)⟩

end Fang.TstpText
