/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Actual mixed declaration decoding preserves ordered named token syntax. -/
import EqualityQuantifiedFormula
import EqualityQuantifiedScope
import EqualityClauseGrammar

namespace Fang.QuantifiedEqualityFrontend
open Frontend EqualityFrontend NamedQuantifiedEquality
open NamedQuantifiedEquality.Grammar

def FofTailRun (fuel : Nat) (name : String) (state : State)
    (parsed : Declaration) (final : State) : Prop :=
  (do
    expect ","
    if (← peek) != some "axiom" then fail "unsupported: only axiom role"
    expect "axiom"
    expect ","
    let body ← formula fuel 0
    if !formulaWithin [] body then fail "invalid-syntax: free FOF variable"
    if (← peek) == some "," then fail "unsupported: source annotations"
    expect ")"
    expect "."
    pure (.fof name body) : Parser Declaration) state = .ok (parsed, final)

theorem fof_tail_grammar {fuel name state parsed final}
    (success : FofTailRun fuel name state parsed final) :
    ∃ body input, parsed = .fof name body ∧ body.Within [] ∧
      spellings state = "," :: "axiom" :: "," :: input ∧
      FormulaTokens input body (")" :: "." :: spellings final) := by
  unfold FofTailRun at success
  obtain ⟨ignored, afterComma, commaRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨role, peekState, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  split at success
  · simp [bind, StateT.bind, fail_run, Except.bind] at success
  · obtain ⟨ignored, afterRole, roleRun, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨ignored, nextComma, nextCommaRun, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨body, afterBody, bodyRun, success⟩ := parser_bind_success success
    have grammar := formula_grammar fuel bodyRun
    split at success
    · simp [bind, StateT.bind, fail_run, Except.bind] at success
    · rename_i closed
      have closedBool : formulaWithin [] body = true := by simpa using closed
      obtain ⟨next, beforeAnnotation, annotationPeek, success⟩ := parser_bind_success success
      rw [peek_run] at annotationPeek
      cases annotationPeek
      split at success
      · simp [bind, StateT.bind, fail_run, Except.bind] at success
      · obtain ⟨ignored, closedState, closing, success⟩ := parser_bind_success success
        cases ignored
        obtain ⟨ignored, periodState, periodRun, success⟩ := parser_bind_success success
        cases ignored
        cases Except.ok.inj success
        refine ⟨body, spellings nextComma, rfl,
          (formulaWithin_correct [] body).mp closedBool, ?_, ?_⟩
        · rw [expect_spellings commaRun, expect_spellings roleRun, expect_spellings nextCommaRun]
        · rw [expect_spellings closing, expect_spellings periodRun] at grammar
          exact grammar

theorem statement_grammar {fuel state parsed final}
    (success : statement fuel state = .ok (parsed, final)) :
    DeclarationTokens (spellings state) parsed (spellings final) := by
  unfold statement at success
  obtain ⟨next, before, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  split at success
  · obtain ⟨clause, afterClause, clauseRun, success⟩ := parser_bind_success success
    cases Except.ok.inj success
    exact .cnf (EqualityFrontend.statement_grammar clauseRun)
  · obtain ⟨next, before, peeked, success⟩ := parser_bind_success success
    rw [peek_run] at peeked
    cases peeked
    split at success
    · obtain ⟨ignored, afterFof, fofRun, success⟩ := parser_bind_success success
      cases ignored
      obtain ⟨ignored, opened, openingRun, success⟩ := parser_bind_success success
      cases ignored
      obtain ⟨offset, positioned, positionRun, success⟩ := parser_bind_success success
      rw [position_run] at positionRun
      cases positionRun
      obtain ⟨name, named, consumed, success⟩ := parser_bind_success success
      split at success
      · simp [bind, StateT.bind, failAt_run, Except.bind] at success
      · rename_i validName
        have nameValid : lowerName name = true := by simpa using validName
        simp only [bind, get, getThe, MonadStateOf.get, StateT.bind, StateT.get,
          pure, Except.pure, Except.bind] at success
        split at success
        · simp [bind, StateT.bind, failAt_run, Except.bind] at success
        · have tail : FofTailRun fuel name
              {named with clauseNames := named.clauseNames ++ [name], variables := []} parsed final := success
          obtain ⟨body, input, same, closed, shape, grammar⟩ := fof_tail_grammar tail
          cases same
          change spellings named = _ at shape
          rw [expect_spellings fofRun, expect_spellings openingRun, consume_spellings consumed, shape]
          exact .fof ((lowerName_iff name (lowerName_ascii nameValid)).mp nameValid) grammar closed
    · obtain ⟨kind, before, peeked, success⟩ := parser_bind_success success
      simp [fail_run] at success

theorem statements_grammar {fuel state parsed final}
    (success : statements fuel state = .ok (parsed, final)) :
    DeclarationsTokens (spellings state) parsed ∧ spellings final = [] := by
  induction fuel generalizing state parsed final with
  | zero => simp [statements, fail_run] at success
  | succ fuel ih =>
    simp only [statements] at success
    obtain ⟨next, peekState, peeked, success⟩ := parser_bind_success success
    rw [peek_run] at peeked
    cases peeked
    split at success
    · rename_i empty
      have emptyTokens : state.tokens = [] := by cases shape : state.tokens <;> simp_all
      cases Except.ok.inj success
      simp only [spellings, emptyTokens, List.map_nil]
      exact ⟨.nil, trivial⟩
    · obtain ⟨first, afterFirst, firstRun, success⟩ := parser_bind_success success
      obtain ⟨tail, afterTail, tailRun, success⟩ := parser_bind_success success
      cases Except.ok.inj success
      obtain ⟨tailGrammar, empty⟩ := ih tailRun
      exact ⟨.cons (statement_grammar firstRun) tailGrammar, empty⟩

/-- Exact named token grammar after actual lexing. Byte tokenization and name
    uniqueness are deliberately separate from this statement. -/
theorem decode_named_token_grammar {input parsed}
    (success : decodeNamed input = .ok parsed) :
    ∃ tokens, tokenize input = .ok tokens ∧ DeclarationsTokens (tokens.map Token.text) parsed := by
  unfold decodeNamed at success
  cases tokenRun : tokenize input with
  | error error => simp [tokenRun, bind, Except.bind] at success
  | ok tokens =>
    simp only [tokenRun, bind, Except.bind] at success
    cases parsedRun : statements (tokens.length + 1) {tokens, endOffset := input.utf8ByteSize} with
    | error error => simp [parsedRun] at success
    | ok pair =>
      rcases pair with ⟨problem, final⟩
      simp only [parsedRun] at success
      split at success
      · cases success
      · cases Except.ok.inj success
        exact ⟨tokens, rfl, (statements_grammar parsedRun).1⟩

end Fang.QuantifiedEqualityFrontend
