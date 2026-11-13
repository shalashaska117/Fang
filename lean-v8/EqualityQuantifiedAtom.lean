/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EqualityQuantifiedGrammar
import EqualityLiteralGrammar

namespace Fang.QuantifiedEqualityFrontend
open Frontend EqualityFrontend NamedQuantifiedEquality.Grammar

theorem atom_grammar {fuel state parsed final}
    (success : atom fuel state = .ok (parsed, final)) :
    AtomTokens (spellings state) parsed (spellings final) := by
  unfold atom at success
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
    obtain ⟨operator, afterOperator, operatorRun, success⟩ := parser_bind_success success
    obtain ⟨second, afterSecond, secondRun, success⟩ := parser_bind_success success
    cases Except.ok.inj success
    have consumed := consume_spellings operatorRun
    have operatorHead : afterFirst.tokens.head?.map Token.text = some operator := by
      rw [← spellings_head, consumed]
      rfl
    simp only [operatorHead, beq_iff_eq, Bool.or_eq_true, Option.some.injEq] at equalityOperator
    rw [consumed] at firstGrammar
    rcases equalityOperator with rfl | rfl
    · exact .equal firstGrammar (named_term_grammar secondRun)
    · exact .notEqual firstGrammar (named_term_grammar secondRun)
  · rename_i noEquality
    have stop : EqualitySource.Grammar.PredicateEnd (spellings afterFirst) := by
      simpa [EqualitySource.Grammar.PredicateEnd, spellings_head, Bool.or_eq_true, beq_iff_eq, not_or]
        using noEquality
    cases first with
    | var name => simp [failAt_run] at success
    | app name arguments =>
      cases Except.ok.inj success
      exact .predicate firstGrammar stop

end Fang.QuantifiedEqualityFrontend
