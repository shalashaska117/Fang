/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Grammar and encoding correspondence for the existing literal parser.
-/
import Fang.FrontendLiteralRun

namespace Fang.Frontend

open Source.Grammar

def PolarityTokens (positive : Bool) (input rest : List Source.Grammar.Token) : Prop :=
  if positive then input = rest else input = .negate :: rest

theorem polarity_grammar (state : State) {input : List Source.Grammar.Token}
    (classified : ClassifiedTokens state.tokens input) {positive : Bool} {updated : State}
    (success : (if state.tokens.head?.map Token.text == some "~" then do
      let (_, final) ← expect "~" state
      pure (false, final)
    else .ok (true, state)) = .ok (positive, updated)) :
    ∃ rest, PolarityTokens positive input rest ∧ ClassifiedTokens updated.tokens rest ∧
      TableExtension state updated := by
  split at success
  · cases negated : expect "~" state with
    | error error => simp [negated, bind, Except.bind] at success
    | ok pair =>
        rcases pair with ⟨returnedUnit, final⟩
        cases returnedUnit
        simp [negated, bind, Except.bind, pure, Except.pure] at success
        rcases success with ⟨rfl, rfl⟩
        obtain ⟨rest, shape, finalClass⟩ := expect_punctuation (character := '~') negated classified
          (by simp [RawPunctuation]) .negate .negate
        exact ⟨rest, shape, finalClass, expect_tableExtension negated⟩
  · cases success
    exact ⟨input, rfl, classified, .refl state⟩

def LiteralGrammarResult (before : State) (tokens : List Source.Grammar.Token)
    (encoded : Fang.Literal) (after : State) : Prop :=
  ∃ named rest, TableLiteralEncoding after named encoded ∧ TableExtension before after ∧
    LiteralTokens tokens named rest ∧ ClassifiedTokens after.tokens rest

theorem literal_grammar {fuel state input encoded updated}
    (classified : ClassifiedTokens state.tokens input)
    (success : literal fuel state = .ok (encoded, updated)) :
    LiteralGrammarResult state input encoded updated := by
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
      obtain ⟨atomTokens, polarity, atomClass, prefixExtension⟩ := polarity_grammar state classified prefixRun
      cases consumedRun : consume beforeName with
      | error error => simp [consumedRun, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨name, consumed⟩
          simp only [consumedRun, bind, Except.bind] at success
          cases valid : lowerName name with
          | false => simp [valid, failAt_run] at success
          | true =>
              simp only [valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
              obtain ⟨id, reserved, allocated, allocation, consumedTokens, _⟩ := reserveSymbol_spec true name consumed
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
                      rcases pair with ⟨returnedUnit, final⟩
                      cases returnedUnit
                      simp [arityRun, pure, Except.pure] at success
                      rcases success with ⟨rfl, rfl⟩
                      obtain ⟨raw, raws, tokenShape, text, consumedShape⟩ := consume_success consumedRun
                      rw [tokenShape] at atomClass
                      cases atomClass with
                      | cons head tail =>
                          have typedHead := head.is_lower (by simpa [text] using valid)
                          rw [text] at typedHead
                          subst typedHead
                          rename_i remainingTokens
                          have reservedClass : ClassifiedTokens reserved.tokens remainingTokens := by
                            rw [consumedTokens, consumedShape]
                            exact tail
                          obtain ⟨namedArgs, ending, argsEncoding, argsExtension, atomGrammar, finalClass⟩ :=
                            function_arguments_grammar fuel reserved _ name reservedClass
                              (fun classified success => terms_grammar classified success) argsRun
                          have arityExtension := checkArity_tableExtension true id args.length _ afterArgs final arityRun
                          have allocatedExtension := reserveSymbol_tableExtension true name consumed reserved id allocated
                          have contract := checkArity_success true id args.length _ afterArgs final arityRun
                          have reservedId : symbolIndex name reserved.predicates 0 = some id := by
                            rw [symbolIndex_eq_namedIndex]
                            exact (namedIndex_first_iff _ _ _).mpr allocation.1
                          have finalId := arityExtension.symbols true name id (argsExtension.symbols true name id reservedId)
                          have namedArity : (final.predicates[id]?).map Symbol.arity = some (some namedArgs.length) := by
                            simpa only [argsEncoding.length, symbolTable, ↓reduceIte] using contract.1
                          refine ⟨⟨positive, name, namedArgs⟩, ending,
                            ⟨rfl, finalId, namedArity, argsEncoding.extend arityExtension⟩,
                            prefixExtension.trans ((consume_tableExtension consumedRun).trans
                              (allocatedExtension.trans (argsExtension.trans arityExtension))), ?_,
                            contract.2.2.1 ▸ finalClass⟩
                          cases positive with
                          | false => rw [polarity]; exact .negative atomGrammar
                          | true => rw [polarity]; exact .positive atomGrammar

#print axioms polarity_grammar
#print axioms literal_grammar

end Fang.Frontend
