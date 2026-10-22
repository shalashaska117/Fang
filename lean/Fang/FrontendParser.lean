/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Contracts for the existing parser's primitive transitions and full consumption.
These lemmas do not establish grammar or named-semantic correspondence.
-/
import Fang.Input

namespace Fang.Frontend

theorem peek_run (state : State) :
    peek state = .ok (state.tokens.head?.map Token.text, state) := by
  rfl

theorem fail_run {α : Type} (reason : String) (state : State) :
    fail (α := α) reason state = .error s!"{reason} at byte {match state.tokens with
      | [] => state.endOffset
      | token :: _ => token.offset}" := by
  rfl

theorem failAt_run {α : Type} (offset : Nat) (reason : String) (state : State) :
    failAt (α := α) offset reason state = .error s!"{reason} at byte {offset}" := by
  rfl

theorem consume_run (state : State) :
    consume state = match state.tokens with
      | [] => fail "invalid-syntax: unexpected EOF" state
      | token :: rest => .ok (token.text, { state with tokens := rest }) := by
  cases tokens : state.tokens <;>
    simp [consume, tokens, bind, pure, get, getThe, MonadStateOf.get, set,
      StateT.bind, StateT.get, StateT.pure, StateT.set, Except.pure, Except.bind]

theorem consume_cons (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) :
    consume state = .ok (token.text, { state with tokens := rest }) := by
  rw [consume_run, tokens]

theorem consume_success {state next : State} {text : String}
    (success : consume state = .ok (text, next)) :
    ∃ token rest, state.tokens = token :: rest ∧ token.text = text ∧
      next = { state with tokens := rest } := by
  cases tokens : state.tokens with
  | nil => simp [consume_run, tokens, fail_run] at success
  | cons token rest =>
      rw [consume_cons state token rest tokens] at success
      cases success
      exact ⟨token, rest, rfl, rfl, rfl⟩

theorem expect_run (wanted : String) (state : State) :
    expect wanted state = if state.tokens.head?.map Token.text != some wanted then
      fail s!"invalid-syntax: expected '{wanted}'" state
    else match consume state with
      | .error error => .error error
      | .ok (_, next) => .ok ((), next) := by
  simp only [expect, peek, bind, pure, get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind]
  split
  · rfl
  · cases result : consume state <;>
      simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, result]

theorem statements_run (fuel : Nat) (state : State) :
    statements (fuel + 1) state = (if state.tokens.isEmpty then .ok ([], state)
      else do
        let (first, updated) ← statement fuel state
        let (rest, final) ← statements fuel updated
        pure (first :: rest, final)) := by
  cases tokens : state.tokens <;>
    simp [statements, peek, tokens, bind, pure, get, getThe, MonadStateOf.get,
      StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind]

theorem statements_success_consumes_all {fuel : Nat} {state final : State} {problem : Problem}
    (success : statements fuel state = .ok (problem, final)) :
    final.tokens = [] ∧ problem.length < fuel := by
  induction fuel generalizing state final problem with
  | zero => simp [statements, fail_run] at success
  | succ fuel induction =>
      rw [statements_run] at success
      split at success
      · have same := Except.ok.inj success
        cases same
        simpa using And.intro (List.isEmpty_iff.mp ‹state.tokens.isEmpty = true›) (Nat.zero_lt_succ fuel)
      · cases first : statement fuel state with
        | error error => simp [first, bind, Except.bind] at success
        | ok pair =>
            rcases pair with ⟨clause, updated⟩
            cases rest : statements fuel updated with
            | error error => simp [first, rest, bind, Except.bind] at success
            | ok pair =>
                rcases pair with ⟨clauses, result⟩
                simp [first, rest, bind, Except.bind] at success
                rcases success with ⟨rfl, rfl⟩
                obtain ⟨consumed, count⟩ := induction rest
                exact ⟨consumed, by simpa using Nat.succ_lt_succ count⟩

theorem expect_cons (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) :
    expect token.text state = .ok ((), { state with tokens := rest }) := by
  simp [expect_run, consume_run, tokens]

theorem expect_success {state next : State} {wanted : String}
    (success : expect wanted state = .ok ((), next)) :
    ∃ token rest, state.tokens = token :: rest ∧ token.text = wanted ∧
      next = { state with tokens := rest } := by
  cases tokens : state.tokens with
  | nil => simp [expect_run, tokens, fail_run] at success
  | cons token rest =>
      by_cases text : token.text = wanted
      · subst wanted
        rw [expect_cons state token rest tokens] at success
        cases success
        exact ⟨token, rest, rfl, rfl, rfl⟩
      · simp [expect_run, tokens, text, fail_run] at success

#print axioms consume_success
#print axioms expect_success
#print axioms statements_success_consumes_all

end Fang.Frontend

namespace Fang

theorem decodeProblemWithSignature_success {input : String} {decoded : DecodedProblem}
    (success : decodeProblemWithSignature input = .ok decoded) :
    ∃ tokens state,
      Frontend.tokenize input = .ok tokens ∧
      Frontend.statements (tokens.length + 1) { tokens, endOffset := input.utf8ByteSize } =
        .ok (decoded.problem, state) ∧
      state.tokens = [] ∧
      decoded.problem.length ≤ tokens.length ∧
      decoded.functionArities = state.functions.map (fun symbol => symbol.arity.getD 0) ∧
      decoded.predicateArities = state.predicates.map (fun symbol => symbol.arity.getD 0) := by
  cases tokenized : Frontend.tokenize input with
  | error error => simp [decodeProblemWithSignature, tokenized, bind, Except.bind] at success
  | ok tokens =>
      cases parsed : Frontend.statements (tokens.length + 1)
          { tokens, endOffset := input.utf8ByteSize } with
      | error error => simp [decodeProblemWithSignature, tokenized, parsed, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨problem, state⟩
          simp [decodeProblemWithSignature, tokenized, parsed, bind, Except.bind, pure, Except.pure] at success
          subst decoded
          obtain ⟨consumed, count⟩ := Frontend.statements_success_consumes_all parsed
          exact ⟨tokens, state, rfl, parsed, consumed, Nat.lt_succ_iff.mp count, rfl, rfl⟩

theorem decodeProblem_success {input : String} {problem : Problem}
    (success : decodeProblem input = .ok problem) :
    ∃ decoded : DecodedProblem, decodeProblemWithSignature input = .ok decoded ∧
      decoded.problem = problem := by
  cases decoded : decodeProblemWithSignature input with
  | error error => simp [decodeProblem, decoded, bind, Except.bind] at success
  | ok value =>
      simp [decodeProblem, decoded, bind, Except.bind, pure, Except.pure] at success
      exact ⟨value, rfl, success⟩

#print axioms decodeProblemWithSignature_success
#print axioms decodeProblem_success

end Fang
