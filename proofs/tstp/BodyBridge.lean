/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import SourceLexerBridge
import BodyPrefix

namespace Fang.TstpText

open Source.Grammar

mutual
theorem term_prefix {tokens value rest input suffix}
    (parsed : TermTokens tokens value rest)
    (lexical : SourcePrefix input (tokens.map sourceToken) suffix)
    (nonempty : rest ≠ []) :
    ∃ middle, TstpBody.TermPrefix input value middle ∧
      SourcePrefix middle (rest.map sourceToken) suffix := by
  cases parsed with
  | variableTerm name rest =>
    obtain ⟨middle, read, tail⟩ := lexical.head
    exact ⟨middle, .variableTerm read, tail⟩
  | constant name rest noArguments =>
    obtain ⟨middle, read, tail⟩ := lexical.head
    refine ⟨middle, .constant read ?_, tail⟩
    cases rest with
    | nil => contradiction
    | cons next tokens =>
      obtain ⟨after, nextRead, _⟩ := tail.head
      have notOpen : next ≠ .lparen := by intro same; subst next; exact noArguments rfl
      intro ending opening
      have pair := Option.some.inj (nextRead.symm.trans opening)
      exact sourceToken_not_lparen notOpen (Prod.mk.inj pair).1
  | application name children =>
    obtain ⟨afterName, read, tail⟩ := lexical.head
    obtain ⟨afterOpen, opening, arguments⟩ := tail.head
    obtain ⟨middle, args, remaining⟩ := arguments_prefix children arguments
    exact ⟨middle, .application read opening args, remaining⟩

theorem arguments_prefix {tokens values rest input suffix}
    (parsed : ArgumentsTokens tokens values rest)
    (lexical : SourcePrefix input (tokens.map sourceToken) suffix) :
    ∃ middle, TstpBody.ArgumentsPrefix input values middle ∧
      SourcePrefix middle (rest.map sourceToken) suffix := by
  cases parsed with
  | last head =>
    obtain ⟨afterTerm, term, closing⟩ := term_prefix head lexical (by simp)
    obtain ⟨middle, close, remaining⟩ := closing.head
    exact ⟨middle, .last term close, remaining⟩
  | more head tail =>
    obtain ⟨afterTerm, term, separator⟩ := term_prefix head lexical (by simp)
    obtain ⟨afterComma, comma, argumentTokens⟩ := separator.head
    obtain ⟨middle, arguments, remaining⟩ := arguments_prefix tail argumentTokens
    exact ⟨middle, .more term comma arguments, remaining⟩
end

theorem literal_prefix {tokens value rest input suffix}
    (parsed : LiteralTokens tokens value rest)
    (lexical : SourcePrefix input (tokens.map sourceToken) suffix)
    (nonempty : rest ≠ []) :
    ∃ middle, TstpBody.LiteralPrefix input value middle ∧
      SourcePrefix middle (rest.map sourceToken) suffix := by
  cases parsed with
  | positive atom =>
    obtain ⟨middle, term, remaining⟩ := term_prefix atom lexical nonempty
    exact ⟨middle, .positive term, remaining⟩
  | negative atom =>
    obtain ⟨afterSign, sign, terms⟩ := lexical.head
    obtain ⟨middle, term, remaining⟩ := term_prefix atom terms nonempty
    exact ⟨middle, .negative sign term, remaining⟩

theorem disjunction_prefix {tokens values rest input suffix}
    (parsed : DisjunctionTokens tokens values rest)
    (lexical : SourcePrefix input (tokens.map sourceToken) suffix) :
    ∃ middle, TstpBody.DisjunctionPrefix input values middle ∧
      SourcePrefix middle (rest.map sourceToken) suffix := by
  induction parsed generalizing input with
  | last head =>
    obtain ⟨afterLiteral, literal, closing⟩ := literal_prefix head lexical (by simp)
    obtain ⟨middle, close, remaining⟩ := closing.head
    exact ⟨middle, .last literal close, remaining⟩
  | more head tail ih =>
    obtain ⟨afterLiteral, literal, separator⟩ := literal_prefix head lexical (by simp)
    obtain ⟨afterDisjoin, disjoin, literals⟩ := separator.head
    obtain ⟨middle, rest, remaining⟩ := ih literals
    exact ⟨middle, .more literal disjoin rest, remaining⟩

theorem body_prefix {tokens values rest input suffix}
    (parsed : BodyTokens tokens values rest)
    (lexical : SourcePrefix input (tokens.map sourceToken) suffix) :
    ∃ middle, TstpBody.BodyPrefix input values middle ∧
      SourcePrefix middle (rest.map sourceToken) suffix := by
  cases parsed with
  | falsity rest =>
    obtain ⟨afterFalse, falsity, closing⟩ := lexical.head
    obtain ⟨middle, close, remaining⟩ := closing.head
    exact ⟨middle, .falsity falsity close, remaining⟩
  | disjunction body =>
    obtain ⟨middle, disjunction, remaining⟩ := disjunction_prefix body lexical
    exact ⟨middle, .disjunction disjunction, remaining⟩

theorem clause_prefix {text : String} {values : List Source.Literal}
    (parsed : ClauseBytesParse (spelling text) values)
    (suffix : List Char) (boundary : TstpUnique.WordBoundary suffix) :
    ∃ middle, TstpBody.BodyPrefix (text.toList ++ ')' :: suffix) values middle ∧
      TstpUnique.readToken middle = TstpUnique.readToken suffix := by
  obtain ⟨tokens, lexical, body⟩ := parsed
  have chars : (spelling text).map byteChar = text.toList :=
    spelling_chars text (fun b member =>
      lexical.ascii b (List.mem_append_left _ member))
  obtain ⟨middle, parsedPrefix, remaining⟩ := body_prefix body (source_tokenization lexical suffix boundary)
  refine ⟨middle, ?_, remaining.empty_read⟩
  simpa [List.map_append, chars, byteChar, List.append_assoc] using parsedPrefix

end Fang.TstpText
