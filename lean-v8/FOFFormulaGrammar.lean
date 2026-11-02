/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import FOFTermGrammar
import FOFEncodingBase
import Fang.FrontendLiteralRun
import Fang.FrontendClauseState

namespace Fang.FOFFrontend
open Frontend FOFGrammar

theorem raw_atom_grammar {fuel state encoded updated}
    (notNegated : ¬ (state.tokens.head?.map Token.text == some "~") = true)
    (success : literal fuel state = .ok (encoded, updated)) :
    ∃ name args, TableLiteralEncoding updated ⟨true, name, args⟩ encoded ∧
      TableExtension state updated ∧
      FOFGrammar.TermTokens (spellings state) (.app name args) (spellings updated) := by
  have positiveRun : (if state.tokens.head?.map Token.text == some "~" then do
      let (_, final) ← expect "~" state
      pure (false, final)
    else .ok (true, state)) = Except.ok (true, state) := by
    simp [notNegated]
  rw [literal_run, positiveRun] at success
  simp only [Except.bind] at success
  cases consumedRun : consume state with
  | error error => simp [consumedRun, bind, Except.bind] at success
  | ok pair =>
    rcases pair with ⟨name, consumed⟩
    simp only [consumedRun, bind, Except.bind] at success
    cases valid : lowerName name with
    | false => simp [valid, failAt_run] at success
    | true =>
      simp only [valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
      obtain ⟨id, reserved, allocated, allocation, reservedTokens, _⟩ := reserveSymbol_spec true name consumed
      simp only [allocated] at success
      cases argsRun : (if reserved.tokens.head?.map Token.text == some "(" then do
          let (_, opened) ← expect "(" reserved
          let (args, afterArgs) ← terms fuel opened
          let (_, closed) ← expect ")" afterArgs
          pure (args, closed)
        else .ok ([], reserved)) with
      | error error =>
        simp only [bind, Except.bind] at argsRun
        rw [argsRun] at success
        simp at success
      | ok pair =>
        rcases pair with ⟨args, afterArgs⟩
        simp only [bind, Except.bind] at argsRun
        rw [argsRun] at success
        simp only at success
        cases arityRun : checkArity true id args.length
            ((state.tokens.head?.map Token.offset).getD state.endOffset) afterArgs with
        | error error => simp [arityRun] at success
        | ok pair =>
          rcases pair with ⟨ignored, final⟩
          cases ignored
          simp [arityRun, pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          obtain ⟨namedArgs, argsEncoding, argsExtension, grammar⟩ :=
            raw_function_arguments fuel reserved name ((lowerName_iff _ (lowerName_ascii valid)).mp valid)
              (fun success => raw_terms_grammar success) argsRun
          have arityExtension := checkArity_tableExtension true id args.length _ afterArgs final arityRun
          have allocatedExtension := reserveSymbol_tableExtension true name consumed reserved id allocated
          have contract := checkArity_success true id args.length _ afterArgs final arityRun
          have reservedId : symbolIndex name reserved.predicates 0 = some id := by
            rw [symbolIndex_eq_namedIndex]
            exact (namedIndex_first_iff _ _ _).mpr allocation.1
          have finalId := arityExtension.symbols true name id (argsExtension.symbols true name id reservedId)
          have namedArity : (final.predicates[id]?).map Symbol.arity = some (some namedArgs.length) := by
            simpa only [argsEncoding.length, symbolTable, ↓reduceIte] using contract.1
          refine ⟨name, namedArgs, ⟨rfl, finalId, namedArity, argsEncoding.extend arityExtension⟩,
            (consume_tableExtension consumedRun).trans (allocatedExtension.trans (argsExtension.trans arityExtension)), ?_⟩
          rw [consume_spellings consumedRun]
          simpa only [spellings, reservedTokens, contract.2.2.1] using grammar

theorem discard_consume_shape {state updated : State} {ignored : PUnit}
    (success : discard consume state = .ok (ignored, updated)) :
    ∃ text, spellings state = text :: spellings updated ∧
      state.tokens.head?.map Token.text = some text ∧ TableExtension state updated := by
  cases consumed : consume state with
  | error error =>
    simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, consumed] at success
  | ok pair =>
    rcases pair with ⟨text, final⟩
    simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, consumed] at success
    rcases success with ⟨rfl, rfl⟩
    have shape := consume_spellings consumed
    refine ⟨text, shape, ?_, consume_tableExtension consumed⟩
    rw [← spellings_head, shape]
    rfl

def RawFormulaResult (before : State) (encoded : GroundFOF.Formula) (after : State) : Prop :=
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

theorem raw_formula_ground {fuel state encoded updated}
    (success : formula fuel state = .ok (encoded, updated)) (ground : encoded.Ground) :
    ∃ named, TableFormulaEncoding updated named encoded ∧ named.Ground ∧
      FormulaTokens (spellings state) named (spellings updated) := by
  obtain ⟨named, encoding, _, grammar⟩ := raw_formula_grammar fuel success
  exact ⟨named, encoding, encoding.ground_iff.mp ground, grammar⟩

end Fang.FOFFrontend
