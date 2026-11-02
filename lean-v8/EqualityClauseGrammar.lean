/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Ordered clause and problem grammar for successful named parser runs. -/
import EqualityLiteralGrammar

namespace Fang.EqualityFrontend
open Frontend EqualitySource.Grammar

theorem literals_run (fuel : Nat) (state : State) :
    literals (fuel + 1) state = (do
      let (first, afterFirst) ← literal fuel state
      if afterFirst.tokens.head?.map Token.text == some "|" then do
        let (_, afterSeparator) ← expect "|" afterFirst
        let (rest, final) ← literals fuel afterSeparator
        pure (first :: rest, final)
      else .ok ([first], afterFirst)) := by
  simp only [literals, peek, bind, pure, get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind]
  cases result : literal fuel state with
  | error error => rfl
  | ok pair => dsimp only; split <;> rfl

theorem literals_grammar {fuel state parsed updated}
    (success : literals fuel state = .ok (parsed, updated)) :
    DisjunctionPrefix (spellings state) parsed (spellings updated) := by
  induction fuel generalizing state parsed updated with
  | zero => simp [literals, fail_run] at success
  | succ fuel ih =>
    rw [literals_run] at success
    cases firstRun : literal fuel state with
    | error error => simp [firstRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨first, afterFirst⟩
      simp only [firstRun, bind, Except.bind] at success
      have firstGrammar := literal_grammar firstRun
      split at success
      · cases separatorRun : expect "|" afterFirst with
        | error error => simp [separatorRun] at success
        | ok pair =>
          rcases pair with ⟨ignored, afterSeparator⟩
          cases ignored
          cases tailRun : literals fuel afterSeparator with
          | error error => simp [separatorRun, tailRun] at success
          | ok pair =>
            rcases pair with ⟨tail, final⟩
            simp [separatorRun, tailRun, pure, Except.pure] at success
            rcases success with ⟨rfl, rfl⟩
            rw [expect_spellings separatorRun] at firstGrammar
            exact .more firstGrammar (ih tailRun)
      · rename_i noDisjoin
        cases success
        apply DisjunctionPrefix.last firstGrammar
        rw [spellings_head]
        simpa only [beq_iff_eq] using noDisjoin

theorem closing_grammar {name : String} {body : List EqualitySource.Literal}
    {state final : State} {parsed : EqualitySource.Clause}
    (success : (do
      expect ")"
      if (← peek) == some "," then fail "unsupported: source annotations"
      expect ")"
      expect "."
      pure ⟨name, body⟩ : Parser EqualitySource.Clause) state = .ok (parsed, final)) :
    parsed = ⟨name, body⟩ ∧ spellings state = ")" :: ")" :: "." :: spellings final := by
  obtain ⟨ignored, first, firstRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨next, peekState, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  split at success
  · simp [bind, StateT.bind, fail_run, Except.bind] at success
  · obtain ⟨ignored, second, secondRun, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨ignored, third, periodRun, success⟩ := parser_bind_success success
    cases ignored
    cases Except.ok.inj success
    exact ⟨rfl, by rw [expect_spellings firstRun, expect_spellings secondRun,
      expect_spellings periodRun]⟩

/-- This predicate names the actual remaining commands of statement. -/
def StatementTailRun (fuel : Nat) (name : String) (state : State)
    (parsed : EqualitySource.Clause) (final : State) : Prop :=
  (do
    expect ","
    if (← peek) != some "axiom" then fail "unsupported: only axiom role"
    expect "axiom"
    expect ","
    expect "("
    let body ← if (← peek) == some "$false" then expect "$false"; pure []
      else literals fuel
    expect ")"
    if (← peek) == some "," then fail "unsupported: source annotations"
    expect ")"
    expect "."
    pure ⟨name, body⟩ : Parser EqualitySource.Clause) state = .ok (parsed, final)

theorem tail_grammar {fuel name state parsed final}
    (success : StatementTailRun fuel name state parsed final) :
    parsed.name = name ∧ ∃ input,
      spellings state = "," :: "axiom" :: "," :: "(" :: input ∧
      BodyTokens input parsed.literals (")" :: "." :: spellings final) := by
  unfold StatementTailRun at success
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
    obtain ⟨ignored, opened, openingRun, success⟩ := parser_bind_success success
    cases ignored
    have headerShape : spellings state = "," :: "axiom" :: "," :: "(" :: spellings opened := by
      rw [expect_spellings commaRun, expect_spellings roleRun, expect_spellings nextCommaRun,
        expect_spellings openingRun]
    obtain ⟨next, peekState, peeked, success⟩ := parser_bind_success success
    rw [peek_run] at peeked
    cases peeked
    split at success
    · obtain ⟨ignored, afterFalse, falseRun, success⟩ := parser_bind_success success
      cases ignored
      obtain ⟨body, bodyState, returned, success⟩ := parser_bind_success success
      have same : (([] : List EqualitySource.Literal), afterFalse) = (body, bodyState) := Except.ok.inj returned
      cases same
      obtain ⟨rfl, closingShape⟩ := closing_grammar success
      refine ⟨rfl, spellings opened, headerShape, ?_⟩
      rw [expect_spellings falseRun, closingShape]
      exact .falsity _
    · obtain ⟨body, afterBody, bodyRun, success⟩ := parser_bind_success success
      have bodyGrammar := literals_grammar bodyRun
      obtain ⟨rfl, closingShape⟩ := closing_grammar success
      rw [closingShape] at bodyGrammar
      exact ⟨rfl, spellings opened, headerShape, .disjunction bodyGrammar.body⟩

theorem statement_grammar {fuel state parsed final}
    (success : statement fuel state = .ok (parsed, final)) :
    StatementTokens (spellings state) parsed (spellings final) := by
  simp only [statement] at success
  obtain ⟨next, before, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  by_cases wrongKind : (state.tokens.head?.map Token.text != some "cnf") = true
  · rw [ite_eq_left wrongKind] at success
    simp [bind, StateT.bind, fail_run, Except.bind] at success
  · rw [ite_eq_right wrongKind] at success
    obtain ⟨ignored, afterCnf, cnfRun, success⟩ := parser_bind_success success
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
      · have tail : StatementTailRun fuel name
            {named with clauseNames := named.clauseNames ++ [name], variables := []} parsed final := success
        obtain ⟨namedEqual, input, shape, bodyGrammar⟩ := tail_grammar tail
        change spellings named = _ at shape
        rw [expect_spellings cnfRun, expect_spellings openingRun, consume_spellings consumed, shape]
        cases parsed with
        | mk parsedName body =>
          dsimp only at namedEqual bodyGrammar
          cases namedEqual
          exact .axiom ((lowerName_iff name (lowerName_ascii nameValid)).mp nameValid) bodyGrammar

theorem statements_grammar {fuel state parsed final}
    (success : statements fuel state = .ok (parsed, final)) :
    ProblemTokens (spellings state) parsed ∧ spellings final = [] := by
  induction fuel generalizing state parsed final with
  | zero => simp [statements, fail_run] at success
  | succ fuel ih =>
    simp only [statements] at success
    obtain ⟨next, peekState, peeked, success⟩ := parser_bind_success success
    rw [peek_run] at peeked
    cases peeked
    split at success
    · rename_i empty
      have emptyTokens : state.tokens = [] := by
        cases shape : state.tokens <;> simp_all
      cases Except.ok.inj success
      simp only [spellings, emptyTokens, List.map_nil]
      exact ⟨.nil, trivial⟩
    · obtain ⟨first, afterFirst, firstRun, success⟩ := parser_bind_success success
      obtain ⟨tail, afterTail, tailRun, success⟩ := parser_bind_success success
      cases Except.ok.inj success
      obtain ⟨tailGrammar, empty⟩ := ih tailRun
      exact ⟨.cons (statement_grammar firstRun) tailGrammar, empty⟩

theorem decode_named_token_grammar {input parsed}
    (success : decodeNamed input = .ok parsed) :
    ∃ tokens, tokenize input = .ok tokens ∧ ProblemTokens (tokens.map Token.text) parsed := by
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

end Fang.EqualityFrontend
