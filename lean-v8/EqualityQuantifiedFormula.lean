/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Successful decoder calls produce the same independent named token grammar. -/
import EqualityQuantifiedAtom

namespace Fang.QuantifiedEqualityFrontend
open Frontend EqualityFrontend NamedQuantifiedEquality.Grammar

theorem binders_grammar (fuel : Nat) :
    ∀ {state names updated}, binders fuel state = .ok (names, updated) →
      BindersTokens (spellings state) names (spellings updated) := by
  induction fuel with
  | zero => intro state names updated success; simp [binders, fail_run] at success
  | succ fuel ih =>
    intro state names updated success
    simp only [binders] at success
    obtain ⟨offset, positioned, positionRun, success⟩ := parser_bind_success success
    rw [position_run] at positionRun
    cases positionRun
    obtain ⟨name, consumed, consumedRun, success⟩ := parser_bind_success success
    cases valid : variableName name with
    | false => simp [valid, bind, StateT.bind, failAt_run, Except.bind] at success
    | true =>
      simp only [valid, Bool.not_true, Bool.false_eq_true, ite_false] at success
      have sourceName : Source.Grammar.VariableName name :=
        (variableName_iff name (variableName_ascii valid)).mp valid
      obtain ⟨delimiter, beforeDelimiter, peeked, success⟩ := parser_bind_success success
      rw [peek_run] at peeked
      cases peeked
      split at success
      · obtain ⟨ignored, final, closed, success⟩ := parser_bind_success success
        cases ignored
        cases Except.ok.inj success
        rw [consume_spellings consumedRun, expect_spellings closed]
        exact .last sourceName
      · split at success
        · obtain ⟨ignored, afterComma, comma, success⟩ := parser_bind_success success
          cases ignored
          obtain ⟨tail, final, child, success⟩ := parser_bind_success success
          cases Except.ok.inj success
          rw [consume_spellings consumedRun, expect_spellings comma]
          exact .more sourceName (ih child)
        · split at success <;> simp [fail_run] at success

theorem discard_consume_shape {state updated : State} {ignored : PUnit}
    (success : discard consume state = .ok (ignored, updated)) :
    ∃ text, spellings state = text :: spellings updated ∧ state.tokens.head?.map Token.text = some text := by
  cases consumed : consume state with
  | error error =>
    simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, consumed] at success
  | ok pair =>
    rcases pair with ⟨text, final⟩
    simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, consumed] at success
    rcases success with ⟨rfl, rfl⟩
    have shape := consume_spellings consumed
    refine ⟨text, shape, ?_⟩
    rw [← spellings_head, shape]
    rfl

theorem formula_grammar (fuel : Nat) :
    ∀ {depth state parsed updated}, formula fuel depth state = .ok (parsed, updated) →
      FormulaTokens (spellings state) parsed (spellings updated) := by
  induction fuel with
  | zero => intro depth state parsed updated success; simp [formula, fail_run] at success
  | succ fuel ih =>
    intro depth state parsed updated success
    simp only [formula] at success
    split at success
    · simp [bind, StateT.bind, fail_run, Except.bind] at success
    · obtain ⟨next, before, peeked, success⟩ := parser_bind_success success
      rw [peek_run] at peeked
      cases peeked
      split at success
      · obtain ⟨ignored, final, checked, success⟩ := parser_bind_success success
        cases ignored
        cases Except.ok.inj success
        rw [expect_spellings checked]
        exact .truth _
      · split at success
        · obtain ⟨ignored, final, checked, success⟩ := parser_bind_success success
          cases ignored
          cases Except.ok.inj success
          rw [expect_spellings checked]
          exact .falsity _
        · split at success
          · obtain ⟨ignored, afterNegation, negated, success⟩ := parser_bind_success success
            cases ignored
            obtain ⟨child, final, childRun, success⟩ := parser_bind_success success
            cases Except.ok.inj success
            rw [expect_spellings negated]
            exact .neg (ih childRun)
          · split at success
            · rename_i quantified
              obtain ⟨ignored, afterQuantifier, quantifierConsumed, success⟩ := parser_bind_success success
              obtain ⟨text, quantifierShape, quantifierHead⟩ := discard_consume_shape quantifierConsumed
              obtain ⟨ignored, opened, opening, success⟩ := parser_bind_success success
              cases ignored
              obtain ⟨names, afterBinders, binderRun, success⟩ := parser_bind_success success
              have binderGrammar := binders_grammar fuel binderRun
              obtain ⟨ignored, afterColon, colon, success⟩ := parser_bind_success success
              cases ignored
              obtain ⟨child, final, childRun, success⟩ := parser_bind_success success
              cases Except.ok.inj success
              have childGrammar := ih childRun
              rw [expect_spellings colon] at binderGrammar
              simp only [Bool.or_eq_true, beq_iff_eq] at quantified
              rcases quantified with universal | existential
              · have same : text = "!" := by simpa [quantifierHead] using universal
                subst text
                have flag : (state.tokens.head?.map Token.text == some "!") = true := by simp [quantifierHead]
                simp only [flag]
                rw [quantifierShape, expect_spellings opening]
                exact .all binderGrammar childGrammar
              · have same : text = "?" := by simpa [quantifierHead] using existential
                subst text
                have flag : (state.tokens.head?.map Token.text == some "!") = false := by simp [quantifierHead]
                simp only [flag]
                rw [quantifierShape, expect_spellings opening]
                exact .ex binderGrammar childGrammar
            · split at success
              · obtain ⟨ignored, opened, opening, success⟩ := parser_bind_success success
                cases ignored
                obtain ⟨left, afterLeft, leftRun, success⟩ := parser_bind_success success
                have leftGrammar := ih leftRun
                obtain ⟨operator, positioned, operatorRun, success⟩ := parser_bind_success success
                rw [peek_run] at operatorRun
                cases operatorRun
                split at success
                · rename_i binary
                  obtain ⟨ignored, afterOperator, operatorConsumed, success⟩ := parser_bind_success success
                  obtain ⟨text, operatorShape, operatorHead⟩ := discard_consume_shape operatorConsumed
                  obtain ⟨right, afterRight, rightRun, success⟩ := parser_bind_success success
                  have rightGrammar := ih rightRun
                  obtain ⟨ignored, final, closing, success⟩ := parser_bind_success success
                  cases ignored
                  rw [expect_spellings closing] at rightGrammar
                  split at success
                  · rename_i conjunction
                    cases Except.ok.inj success
                    have same : text = "&" := by simpa [operatorHead] using conjunction
                    subst text
                    rw [operatorShape] at leftGrammar
                    rw [expect_spellings opening]
                    exact .conj leftGrammar rightGrammar
                  · rename_i notConjunction
                    split at success
                    · rename_i disjunction
                      cases Except.ok.inj success
                      have same : text = "|" := by simpa [operatorHead] using disjunction
                      subst text
                      rw [operatorShape] at leftGrammar
                      rw [expect_spellings opening]
                      exact .disj leftGrammar rightGrammar
                    · rename_i notDisjunction
                      cases Except.ok.inj success
                      have same : text = "=>" := by
                        simp only [Bool.or_eq_true, beq_iff_eq] at binary notConjunction notDisjunction
                        rcases binary with (conjunction | disjunction) | implication
                        · exact False.elim (notConjunction conjunction)
                        · exact False.elim (notDisjunction disjunction)
                        · simpa [operatorHead] using implication
                      subst text
                      rw [operatorShape] at leftGrammar
                      rw [expect_spellings opening]
                      exact .implies leftGrammar rightGrammar
                · obtain ⟨ignored, final, closing, success⟩ := parser_bind_success success
                  cases ignored
                  cases Except.ok.inj success
                  rw [expect_spellings opening]
                  rw [expect_spellings closing] at leftGrammar
                  exact .paren leftGrammar
              · exact .atom (atom_grammar success)

end Fang.QuantifiedEqualityFrontend
