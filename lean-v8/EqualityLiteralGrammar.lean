/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Successful equality/predicate literal parsing preserves the named syntax. -/
import EqualityTermGrammar

namespace Fang.EqualityFrontend
open Frontend EqualitySource.Grammar

theorem consume_spellings {state updated : State} {text : String}
    (success : consume state = .ok (text, updated)) :
    spellings state = text :: spellings updated := by
  obtain ⟨token, rest, shape, text, rfl⟩ := consume_success success
  simp [spellings, shape, text]

theorem position_run (state : State) :
    position state = .ok ((state.tokens.head?.map Token.offset).getD state.endOffset, state) := by
  cases shape : state.tokens <;>
    simp [position, shape, bind, pure, get, getThe, MonadStateOf.get,
      StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind]

/-- The literal commands after the optional negation, copied as a proof predicate. -/
def LiteralTailRun (fuel : Nat) (negated : Bool) (state : State)
    (parsed : EqualitySource.Literal) (final : State) : Prop :=
  (do
    let offset ← position
    let first ← namedTerm fuel 0
    let next ← peek
    if next == some "=" || next == some "!=" then
      if negated then fail "unsupported: use infix != for negative equality"
      let operator ← consume
      let second ← namedTerm fuel 0
      pure ⟨operator == "=", .equal first second⟩
    else match first with
      | .var _ => failAt offset "invalid-syntax: variable cannot be a predicate"
      | .app name arguments => pure ⟨!negated, .predicate name arguments⟩
    : Parser EqualitySource.Literal) state = .ok (parsed, final)

theorem literal_tail_grammar {fuel negated state parsed final}
    (success : LiteralTailRun fuel negated state parsed final) :
    LiteralTokens ((if negated then ["~"] else []) ++ spellings state) parsed (spellings final) := by
  unfold LiteralTailRun at success
  obtain ⟨offset, positioned, positionRun, success⟩ := parser_bind_success success
  rw [position_run] at positionRun
  cases positionRun
  obtain ⟨first, afterFirst, firstRun, success⟩ := parser_bind_success success
  have firstGrammar := named_term_grammar firstRun
  obtain ⟨next, peekState, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  split at success
  · rename_i equalityOperator
    cases negated with
    | true => simp [bind, StateT.bind, fail_run, Except.bind] at success
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at success
      obtain ⟨operator, afterOperator, operatorRun, success⟩ := parser_bind_success success
      obtain ⟨second, afterSecond, secondRun, success⟩ := parser_bind_success success
      cases Except.ok.inj success
      have consumed := consume_spellings operatorRun
      have operatorHead : afterFirst.tokens.head?.map Token.text = some operator := by
        rw [← spellings_head, consumed]
        rfl
      simp only [operatorHead, beq_iff_eq, Bool.or_eq_true, Option.some.injEq] at equalityOperator
      rw [consumed] at firstGrammar
      simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
      rcases equalityOperator with rfl | rfl
      · exact .equal firstGrammar (named_term_grammar secondRun)
      · exact .notEqual firstGrammar (named_term_grammar secondRun)
  · rename_i noEquality
    have stop : PredicateEnd (spellings afterFirst) := by
      simpa [PredicateEnd, spellings_head, Bool.or_eq_true, beq_iff_eq, not_or] using noEquality
    cases first with
    | var name => simp [failAt_run] at success
    | app name arguments =>
      cases Except.ok.inj success
      cases negated with
      | false => exact .predicate firstGrammar stop
      | true => exact .negative firstGrammar stop

theorem literal_grammar {fuel state parsed updated}
    (success : literal fuel state = .ok (parsed, updated)) :
    LiteralTokens (spellings state) parsed (spellings updated) := by
  simp only [literal] at success
  obtain ⟨next, peekState, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  split at success
  · obtain ⟨ignored, afterNegation, negationRun, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨negated, nextState, returned, success⟩ := parser_bind_success success
    cases Except.ok.inj returned
    have grammar := literal_tail_grammar (show LiteralTailRun fuel true afterNegation parsed updated from success)
    rw [expect_spellings negationRun]
    exact grammar
  · obtain ⟨negated, nextState, returned, success⟩ := parser_bind_success success
    cases Except.ok.inj returned
    exact literal_tail_grammar (show LiteralTailRun fuel false state parsed updated from success)

end Fang.EqualityFrontend

