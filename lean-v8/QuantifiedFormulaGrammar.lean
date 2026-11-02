/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Decoder construction proof draft, extending Fang's accepted ground formula
   proof with nested quantifiers. Not part of an accepted gate yet. -/
import QuantifiedBinders
import QuantifiedTableEncoding
import FOFFormulaGrammar

namespace Fang.QuantifiedFrontend
open Frontend FOFFrontend NamedQuantified.Grammar

def RawFormulaResult (before : State) (encoded : QuantifiedFOF.Formula) (after : State) : Prop :=
  ∃ named, TableFormulaEncoding after named encoded ∧ TableExtension before after ∧
    FormulaTokens (spellings before) named (spellings after)

theorem raw_formula_grammar (fuel : Nat) :
    ∀ {state encoded updated}, formula fuel state = .ok (encoded, updated) →
      RawFormulaResult state encoded updated := by
  induction fuel with
  | zero => intro state encoded updated success; simp [formula, fail_run] at success
  | succ fuel ih =>
    intro state encoded updated success
    simp only [formula] at success
    obtain ⟨next, before, peeked, success⟩ := parser_bind_success success
    rw [peek_run] at peeked
    cases peeked
    split at success
    · obtain ⟨ignored, final, checked, success⟩ := parser_bind_success success
      cases ignored
      cases Except.ok.inj success
      refine ⟨.truth, .truth, expect_tableExtension checked, ?_⟩
      rw [expect_spellings checked]
      exact .truth _
    · split at success
      · obtain ⟨ignored, final, checked, success⟩ := parser_bind_success success
        cases ignored
        cases Except.ok.inj success
        refine ⟨.falsity, .falsity, expect_tableExtension checked, ?_⟩
        rw [expect_spellings checked]
        exact .falsity _
      · split at success
        · obtain ⟨ignored, afterNegation, negated, success⟩ := parser_bind_success success
          cases ignored
          obtain ⟨child, final, parsed, success⟩ := parser_bind_success success
          cases Except.ok.inj success
          obtain ⟨named, encoding, extension, grammar⟩ := ih parsed
          refine ⟨.neg named, .neg encoding, (expect_tableExtension negated).trans extension, ?_⟩
          rw [expect_spellings negated]
          exact .neg grammar
        · rename_i notNegated
          split at success
          · rename_i quantified
            obtain ⟨ignored, afterQuantifier, quantifierConsumed, success⟩ := parser_bind_success success
            obtain ⟨text, quantifierShape, quantifierHead, quantifierExtension⟩ :=
              discard_consume_shape quantifierConsumed
            obtain ⟨ignored, opened, opening, success⟩ := parser_bind_success success
            cases ignored
            obtain ⟨ids, afterBinders, binderRun, success⟩ := parser_bind_success success
            obtain ⟨names, binderEncoding, binderExtension, binderGrammar⟩ := binders_result fuel binderRun
            obtain ⟨ignored, afterColon, colon, success⟩ := parser_bind_success success
            cases ignored
            obtain ⟨child, final, childRun, success⟩ := parser_bind_success success
            cases Except.ok.inj success
            obtain ⟨named, childEncoding, childExtension, childGrammar⟩ := ih childRun
            have colonExtension := expect_tableExtension colon
            have finalBinders := BoundEncoding.ofRelated
              (binderEncoding.extend (colonExtension.trans childExtension))
            have wholeExtension := quantifierExtension.trans ((expect_tableExtension opening).trans
              (binderExtension.trans (colonExtension.trans childExtension)))
            rw [expect_spellings colon] at binderGrammar
            simp only [Bool.or_eq_true, beq_iff_eq] at quantified
            rcases quantified with universal | existential
            · have textEq : text = "!" := by simpa [quantifierHead] using universal
              subst text
              have flag : (state.tokens.head?.map Token.text == some "!") = true := by simp [quantifierHead]
              refine ⟨named.bind true names, ?_, wholeExtension, ?_⟩
              · simpa only [NamedQuantified.Formula.bind, flag] using childEncoding.bind true finalBinders
              · rw [quantifierShape, expect_spellings opening]
                exact .all binderGrammar childGrammar
            · have textEq : text = "?" := by simpa [quantifierHead] using existential
              subst text
              have flag : (state.tokens.head?.map Token.text == some "!") = false := by simp [quantifierHead]
              refine ⟨named.bind false names, ?_, wholeExtension, ?_⟩
              · simpa only [NamedQuantified.Formula.bind, flag] using childEncoding.bind false finalBinders
              · rw [quantifierShape, expect_spellings opening]
                exact .ex binderGrammar childGrammar
          ·
            split at success
            · obtain ⟨ignored, opened, opening, success⟩ := parser_bind_success success
              cases ignored
              obtain ⟨left, afterLeft, leftRun, success⟩ := parser_bind_success success
              obtain ⟨namedLeft, leftEncoding, leftExtension, leftGrammar⟩ := ih leftRun
              obtain ⟨operator, positioned, operatorRun, success⟩ := parser_bind_success success
              rw [peek_run] at operatorRun
              cases operatorRun
              split at success
              · rename_i binary
                obtain ⟨ignored, afterOperator, operatorConsumed, success⟩ := parser_bind_success success
                obtain ⟨text, operatorShape, operatorHead, operatorExtension⟩ := discard_consume_shape operatorConsumed
                obtain ⟨right, afterRight, rightRun, success⟩ := parser_bind_success success
                obtain ⟨namedRight, rightEncoding, rightExtension, rightGrammar⟩ := ih rightRun
                obtain ⟨ignored, final, closing, success⟩ := parser_bind_success success
                cases ignored
                have finalExtension := expect_tableExtension closing
                have leftFinal := leftEncoding.extend (operatorExtension.trans (rightExtension.trans finalExtension))
                have rightFinal := rightEncoding.extend finalExtension
                have wholeExtension := (expect_tableExtension opening).trans
                  (leftExtension.trans (operatorExtension.trans (rightExtension.trans finalExtension)))
                rw [expect_spellings closing] at rightGrammar
                split at success
                · rename_i conjunction
                  cases Except.ok.inj success
                  have textEq : text = "&" := by simpa [operatorHead] using conjunction
                  subst text
                  rw [operatorShape] at leftGrammar
                  refine ⟨.conj namedLeft namedRight, .conj leftFinal rightFinal, wholeExtension, ?_⟩
                  rw [expect_spellings opening]
                  exact .conj leftGrammar rightGrammar
                · rename_i notConjunction
                  split at success
                  · rename_i disjunction
                    cases Except.ok.inj success
                    have textEq : text = "|" := by simpa [operatorHead] using disjunction
                    subst text
                    rw [operatorShape] at leftGrammar
                    refine ⟨.disj namedLeft namedRight, .disj leftFinal rightFinal, wholeExtension, ?_⟩
                    rw [expect_spellings opening]
                    exact .disj leftGrammar rightGrammar
                  · rename_i notDisjunction
                    cases Except.ok.inj success
                    have textEq : text = "=>" := by
                      simp only [Bool.or_eq_true, beq_iff_eq] at binary notConjunction notDisjunction
                      rcases binary with (conjunction | disjunction) | implication
                      · exact False.elim (notConjunction conjunction)
                      · exact False.elim (notDisjunction disjunction)
                      · simpa [operatorHead] using implication
                    subst text
                    rw [operatorShape] at leftGrammar
                    refine ⟨.implies namedLeft namedRight, .implies leftFinal rightFinal, wholeExtension, ?_⟩
                    rw [expect_spellings opening]
                    exact .implies leftGrammar rightGrammar
              · obtain ⟨ignored, final, closing, success⟩ := parser_bind_success success
                cases ignored
                cases Except.ok.inj success
                have finalExtension := expect_tableExtension closing
                refine ⟨namedLeft, leftEncoding.extend finalExtension,
                  (expect_tableExtension opening).trans (leftExtension.trans finalExtension), ?_⟩
                rw [expect_spellings opening]
                rw [expect_spellings closing] at leftGrammar
                exact .paren leftGrammar
            · cases nextShape : state.tokens.head?.map Token.text with
              | none => simp [nextShape, fail_run] at success
              | some name =>
                simp only [nextShape] at success
                split at success
                · simp [fail_run] at success
                · split at success
                  · obtain ⟨atom, final, parsed, success⟩ := parser_bind_success success
                    cases Except.ok.inj success
                    obtain ⟨predicate, args, encoding, extension, grammar⟩ := raw_atom_grammar notNegated parsed
                    exact ⟨.atom predicate args,
                      .atom predicate atom.atom.pred args atom.atom.args
                        encoding.found encoding.checked encoding.arguments, extension, .atom grammar⟩
                  · simp [fail_run] at success

theorem raw_formula_closed {fuel state encoded updated}
    (success : formula fuel state = .ok (encoded, updated)) (closed : formulaWithin [] encoded = true) :
    ∃ named, TableFormulaEncoding updated named encoded ∧ named.Within [] ∧
      FormulaTokens (spellings state) named (spellings updated) := by
  obtain ⟨named, encoding, _, grammar⟩ := raw_formula_grammar fuel success
  exact ⟨named, encoding, encoding.closed_of_formulaWithin closed, grammar⟩

end Fang.QuantifiedFrontend
