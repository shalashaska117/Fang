/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Composition of actual statement parsing with independent named-source grammar.
-/
import Fang.FrontendDisjunctionGrammar
import Fang.FrontendClauseState
import Fang.FrontendSymbolExtension

namespace Fang.Frontend

open Source.Grammar

theorem expect_lower_name {state updated : State} {name : String}
    (success : expect name state = .ok ((), updated))
    {tokens : List Source.Grammar.Token} (classified : ClassifiedTokens state.tokens tokens)
    (valid : lowerName name = true) :
    ∃ rest, tokens = .lower name :: rest ∧ ClassifiedTokens updated.tokens rest := by
  obtain ⟨raw, raws, shape, text, rfl⟩ := expect_success success
  rw [shape] at classified
  cases classified with
  | cons head tail =>
      have same := head.is_lower (by simpa [text] using valid)
      rw [text] at same
      exact ⟨_, congrArg (fun first => first :: _) same, tail⟩

theorem expect_false_literal {state updated : State}
    (success : expect "$false" state = .ok ((), updated))
    {tokens : List Source.Grammar.Token} (classified : ClassifiedTokens state.tokens tokens) :
    ∃ rest, tokens = .falseLiteral :: rest ∧ ClassifiedTokens updated.tokens rest := by
  obtain ⟨raw, raws, shape, text, rfl⟩ := expect_success success
  rw [shape] at classified
  cases classified with
  | cons head tail =>
      have same := head.unique (rawTokenSpelling_false raw text)
      exact ⟨_, congrArg (fun first => first :: _) same, tail⟩

def StatementClosingRun (body : Clause) (state final : State) (result : Clause) : Prop :=
  (do
    expect ")"
    expect ")"
    expect "."
    pure body : Parser Clause) state = .ok (result, final)

theorem statement_closing_grammar {state final : State} {body result : Clause}
    {tokens : List Source.Grammar.Token} (classified : ClassifiedTokens state.tokens tokens)
    (success : StatementClosingRun body state final result) :
    ∃ rest, tokens = .rparen :: .rparen :: .period :: rest ∧
      ClassifiedTokens final.tokens rest ∧ TableExtension state final ∧ result = body := by
  unfold StatementClosingRun at success
  obtain ⟨ignored, firstClosed, firstRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨firstRest, firstShape, firstClass⟩ := expect_punctuation (character := ')') firstRun classified
    (by simp [RawPunctuation]) .rparen .rparen
  obtain ⟨ignored, secondClosed, secondRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨secondRest, secondShape, secondClass⟩ := expect_punctuation (character := ')') secondRun firstClass
    (by simp [RawPunctuation]) .rparen .rparen
  obtain ⟨ignored, dotted, periodRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨rest, periodShape, finalClass⟩ := expect_punctuation (character := '.') periodRun secondClass
    (by simp [RawPunctuation]) .period .period
  have same : (body, dotted) = (result, final) := Except.ok.inj success
  cases same
  exact ⟨rest, by rw [firstShape, secondShape, periodShape], finalClass,
    (expect_tableExtension firstRun).trans
      ((expect_tableExtension secondRun).trans (expect_tableExtension periodRun)), rfl⟩

def TailGrammarResult (before : State) (tokens : List Source.Grammar.Token)
    (encoded : Clause) (after : State) : Prop :=
  ∃ named rest bodyInput,
    tokens = .comma :: .lower "axiom" :: .comma :: .lparen :: bodyInput ∧
    BodyTokens bodyInput named (.rparen :: .period :: rest) ∧
    TableClauseEncoding after named encoded ∧ TableExtension before after ∧
    ClassifiedTokens after.tokens rest

theorem statement_tail_grammar {fuel state input encoded updated}
    (classified : ClassifiedTokens state.tokens input)
    (success : StatementTailRun fuel state encoded updated) :
    TailGrammarResult state input encoded updated := by
  unfold StatementTailRun at success
  obtain ⟨ignored, afterComma, commaRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨commaRest, commaShape, commaClass⟩ := expect_punctuation (character := ',') commaRun classified
    (by simp [RawPunctuation]) .comma .comma
  obtain ⟨role, roleState, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  split at success
  · simp [bind, StateT.bind, fail_run, Except.bind] at success
  · obtain ⟨ignored, afterRole, roleRun, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨roleRest, roleShape, roleClass⟩ := expect_lower_name roleRun commaClass (by decide)
    obtain ⟨ignored, nextComma, nextCommaRun, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨nextCommaRest, nextCommaShape, nextCommaClass⟩ :=
      expect_punctuation (character := ',') nextCommaRun roleClass (by simp [RawPunctuation]) .comma .comma
    obtain ⟨ignored, opened, openingRun, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨bodyInput, openingShape, bodyClass⟩ :=
      expect_punctuation (character := '(') openingRun nextCommaClass (by simp [RawPunctuation]) .lparen .lparen
    have headerShape : input = .comma :: .lower "axiom" :: .comma :: .lparen :: bodyInput := by
      rw [commaShape, roleShape, nextCommaShape, openingShape]
    have headerExtension := (expect_tableExtension commaRun).trans
      ((expect_tableExtension roleRun).trans ((expect_tableExtension nextCommaRun).trans
        (expect_tableExtension openingRun)))
    obtain ⟨next, peekState, peeked, success⟩ := parser_bind_success success
    rw [peek_run] at peeked
    cases peeked
    split at success
    · obtain ⟨ignored, afterFalse, falseRun, success⟩ := parser_bind_success success
      cases ignored
      obtain ⟨falseRest, falseShape, falseClass⟩ := expect_false_literal falseRun bodyClass
      obtain ⟨body, bodyState, returned, success⟩ := parser_bind_success success
      have same : (([] : Clause), afterFalse) = (body, bodyState) := Except.ok.inj returned
      cases same
      obtain ⟨rest, endingShape, finalClass, closingExtension, rfl⟩ :=
        statement_closing_grammar falseClass success
      refine ⟨[], rest, bodyInput, headerShape, ?_, .nil,
        headerExtension.trans ((expect_tableExtension falseRun).trans closingExtension), finalClass⟩
      rw [falseShape, endingShape]
      exact .falsity _
    · obtain ⟨body, afterBody, bodyRun, success⟩ := parser_bind_success success
      obtain ⟨named, bodyRest, encoding, bodyExtension, bodyGrammar, afterBodyClass⟩ :=
        literals_grammar bodyClass bodyRun
      obtain ⟨rest, endingShape, finalClass, closingExtension, rfl⟩ :=
        statement_closing_grammar afterBodyClass success
      exact ⟨named, rest, bodyInput, headerShape,
        .disjunction ((endingShape ▸ bodyGrammar).body), encoding.extend closingExtension,
        headerExtension.trans (bodyExtension.trans closingExtension), finalClass⟩

def StatementGrammarResult (before : State) (tokens : List Source.Grammar.Token)
    (encoded : Clause) (after : State) : Prop :=
  ∃ named rest, TableClauseEncoding after named.literals encoded ∧ SymbolExtension before after ∧
    StatementTokens tokens named rest ∧ ClassifiedTokens after.tokens rest ∧
    named.name ∉ before.clauseNames ∧ after.clauseNames = before.clauseNames ++ [named.name]

theorem statement_grammar {fuel state input encoded updated}
    (classified : ClassifiedTokens state.tokens input)
    (success : statement fuel state = .ok (encoded, updated)) :
    StatementGrammarResult state input encoded updated := by
  obtain ⟨name, afterCnf, opened, namedState, cnfRun, openingRun, nameRun, valid,
    fresh, priorNames, priorVariables, tailRun⟩ := statement_success_decomposition success
  obtain ⟨cnfRest, cnfShape, cnfClass⟩ := expect_lower_name cnfRun classified (by decide)
  obtain ⟨openRest, openShape, openClass⟩ := expect_punctuation (character := '(') openingRun cnfClass
    (by simp [RawPunctuation]) .lparen .lparen
  obtain ⟨raw, raws, nameTokens, text, namedShape⟩ := consume_success nameRun
  rw [nameTokens] at openClass
  cases openClass with
  | cons head tail =>
      have typedHead := head.is_lower (by simpa [text] using valid)
      rw [text] at typedHead
      subst typedHead
      rename_i remainingTokens
      have tailClass : ClassifiedTokens
          { namedState with clauseNames := namedState.clauseNames ++ [name], variables := [] }.tokens
          remainingTokens := by
        rw [namedShape]
        exact tail
      obtain ⟨namedLiterals, ending, bodyInput, tailShape, bodyGrammar, encoding, tailExtension, finalClass⟩ :=
        statement_tail_grammar tailClass tailRun
      have headerExtension := (expect_tableExtension cnfRun).trans
        ((expect_tableExtension openingRun).trans (consume_tableExtension nameRun))
      refine ⟨⟨name, namedLiterals⟩, ending, encoding,
        headerExtension.toSymbolExtension.trans
          ((symbolExtension_reset namedState [] (namedState.clauseNames ++ [name])).trans
            tailExtension.toSymbolExtension), ?_, finalClass, ?_, ?_⟩
      · rw [cnfShape, openShape, tailShape]
        exact .statement name bodyGrammar
      · simpa only [priorNames] using fresh
      · simpa only [priorNames] using tailRun.clause_names

#print axioms statement_closing_grammar
#print axioms statement_tail_grammar
#print axioms statement_grammar

end Fang.Frontend
