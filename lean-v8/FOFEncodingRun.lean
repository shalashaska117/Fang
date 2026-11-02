/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import FOFEncodingBase
import Fang.FrontendLiteralRun
import Fang.FrontendRecursiveEncoding
import Fang.FrontendClauseState

namespace Fang.FOFFrontend
open Frontend

def LiteralResult (before : State) (encoded : Fang.Literal) (after : State) : Prop :=
  ∃ named, TableLiteralEncoding after named encoded ∧ TableExtension before after

theorem literal_result {fuel state encoded updated}
    (success : literal fuel state = .ok (encoded, updated)) :
    LiteralResult state encoded updated := by
  rw [literal_run] at success
  cases prefixRun : (if state.tokens.head?.map Token.text == some "~" then do
      let (_, final) ← expect "~" state
      pure (false, final)
    else .ok (true, state)) with
  | error error => rw [prefixRun] at success; simp [Except.bind] at success
  | ok pair =>
      rcases pair with ⟨positive, beforeName⟩
      rw [prefixRun] at success
      simp only [Except.bind] at success
      have prefixExtension : TableExtension state beforeName := by
        split at prefixRun
        · cases negated : expect "~" state with
          | error error => simp [negated, bind, Except.bind] at prefixRun
          | ok pair =>
              rcases pair with ⟨ignored, final⟩
              cases ignored
              simp [negated, bind, Except.bind, pure, Except.pure] at prefixRun
              rcases prefixRun with ⟨rfl, rfl⟩
              exact expect_tableExtension negated
        · cases prefixRun
          exact .refl state
      cases consumedRun : consume beforeName with
      | error error => simp [consumedRun, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨name, consumed⟩
          simp only [consumedRun, bind, Except.bind] at success
          cases valid : lowerName name with
          | false => simp [valid, failAt_run] at success
          | true =>
              simp only [valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
              obtain ⟨id, reserved, allocated, allocation, _, _⟩ := reserveSymbol_spec true name consumed
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
                      ((beforeName.tokens.head?.map Token.offset).getD beforeName.endOffset) afterArgs with
                  | error error => simp [arityRun] at success
                  | ok pair =>
                      rcases pair with ⟨ignored, final⟩
                      cases ignored
                      simp [arityRun, pure, Except.pure] at success
                      rcases success with ⟨rfl, rfl⟩
                      obtain ⟨namedArgs, argsEncoding, argsExtension⟩ :=
                        function_arguments_result fuel reserved reserved.tokens
                          (fun success => terms_result success) argsRun
                      have arityExtension := checkArity_tableExtension true id args.length _ afterArgs final arityRun
                      have allocatedExtension := reserveSymbol_tableExtension true name consumed reserved id allocated
                      have contract := checkArity_success true id args.length _ afterArgs final arityRun
                      have reservedId : symbolIndex name reserved.predicates 0 = some id := by
                        rw [symbolIndex_eq_namedIndex]
                        exact (namedIndex_first_iff _ _ _).mpr allocation.1
                      have finalId := arityExtension.symbols true name id (argsExtension.symbols true name id reservedId)
                      have namedArity : (final.predicates[id]?).map Symbol.arity = some (some namedArgs.length) := by
                        simpa only [argsEncoding.length, symbolTable, ↓reduceIte] using contract.1
                      exact ⟨⟨positive, name, namedArgs⟩,
                        ⟨rfl, finalId, namedArity, argsEncoding.extend arityExtension⟩,
                        prefixExtension.trans ((consume_tableExtension consumedRun).trans
                          (allocatedExtension.trans (argsExtension.trans arityExtension)))⟩

def FormulaResult (before : State) (encoded : GroundFOF.Formula) (after : State) : Prop :=
  ∃ named, TableFormulaEncoding after named encoded ∧ TableExtension before after

theorem formula_result (fuel : Nat) :
    ∀ {state encoded updated}, formula fuel state = .ok (encoded, updated) →
      FormulaResult state encoded updated := by
  induction fuel with
  | zero =>
      intro state encoded updated success
      simp [formula, fail_run] at success
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
        exact ⟨.truth, .truth, expect_tableExtension checked⟩
      · split at success
        · obtain ⟨ignored, final, checked, success⟩ := parser_bind_success success
          cases ignored
          cases Except.ok.inj success
          exact ⟨.falsity, .falsity, expect_tableExtension checked⟩
        · split at success
          · obtain ⟨ignored, afterNegation, negated, success⟩ := parser_bind_success success
            cases ignored
            obtain ⟨child, final, parsed, success⟩ := parser_bind_success success
            cases Except.ok.inj success
            obtain ⟨named, encoding, extension⟩ := ih parsed
            exact ⟨.neg named, .neg encoding, (expect_tableExtension negated).trans extension⟩
          · split at success
            · obtain ⟨ignored, opened, opening, success⟩ := parser_bind_success success
              cases ignored
              obtain ⟨left, afterLeft, leftRun, success⟩ := parser_bind_success success
              obtain ⟨namedLeft, leftEncoding, leftExtension⟩ := ih leftRun
              obtain ⟨operator, positioned, operatorRun, success⟩ := parser_bind_success success
              rw [peek_run] at operatorRun
              cases operatorRun
              split at success
              · obtain ⟨ignored, afterOperator, operatorConsumed, success⟩ := parser_bind_success success
                have operatorExtension : TableExtension afterLeft afterOperator := by
                  cases consumed : consume afterLeft with
                  | error error =>
                      simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map,
                        consumed] at operatorConsumed
                  | ok pair =>
                      rcases pair with ⟨text, final⟩
                      simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map,
                        consumed] at operatorConsumed
                      rcases operatorConsumed with ⟨rfl, rfl⟩
                      exact consume_tableExtension consumed
                obtain ⟨right, afterRight, rightRun, success⟩ := parser_bind_success success
                obtain ⟨namedRight, rightEncoding, rightExtension⟩ := ih rightRun
                obtain ⟨ignored, final, closing, success⟩ := parser_bind_success success
                cases ignored
                have finalExtension := expect_tableExtension closing
                have leftFinal := leftEncoding.extend (operatorExtension.trans (rightExtension.trans finalExtension))
                have rightFinal := rightEncoding.extend finalExtension
                have wholeExtension := (expect_tableExtension opening).trans
                  (leftExtension.trans (operatorExtension.trans (rightExtension.trans finalExtension)))
                split at success
                · cases Except.ok.inj success
                  exact ⟨.conj namedLeft namedRight, .conj leftFinal rightFinal, wholeExtension⟩
                · split at success
                  · cases Except.ok.inj success
                    exact ⟨.disj namedLeft namedRight, .disj leftFinal rightFinal, wholeExtension⟩
                  · cases Except.ok.inj success
                    exact ⟨.implies namedLeft namedRight, .implies leftFinal rightFinal, wholeExtension⟩
              · obtain ⟨ignored, final, closing, success⟩ := parser_bind_success success
                cases ignored
                cases Except.ok.inj success
                have finalExtension := expect_tableExtension closing
                exact ⟨namedLeft, leftEncoding.extend finalExtension,
                  (expect_tableExtension opening).trans (leftExtension.trans finalExtension)⟩
            · cases nextShape : state.tokens.head?.map Token.text with
              | none => simp [nextShape, fail_run] at success
              | some name =>
                  simp only [nextShape] at success
                  split at success
                  · simp [fail_run] at success
                  · split at success
                    · obtain ⟨atom, final, parsed, success⟩ := parser_bind_success success
                      cases Except.ok.inj success
                      obtain ⟨named, encoding, extension⟩ := literal_result parsed
                      exact ⟨.atom named.predicate named.arguments,
                        .atom named.predicate atom.atom.pred named.arguments atom.atom.args
                          encoding.found encoding.checked encoding.arguments, extension⟩
                    · simp [fail_run] at success

theorem formula_named_encoding {fuel state encoded updated}
    (success : formula fuel state = .ok (encoded, updated)) :
    ∃ named, NamedFOF.Encoding (signatureFrom updated) (symbolsFrom updated)
      (variablesFrom updated.variables) named encoded ∧
      (encoded.Ground ↔ named.Ground) ∧ TableExtension state updated := by
  obtain ⟨named, encoding, extension⟩ := formula_result fuel success
  exact ⟨named, encoding.toSource, encoding.ground_iff, extension⟩

end Fang.FOFFrontend
