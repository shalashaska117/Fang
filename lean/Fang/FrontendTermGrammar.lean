/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Successful term parsing agrees with the independent source-token grammar.
The parser and grammar remain separate definitions.
-/
import Fang.FrontendRecursiveEncoding
import Fang.FrontendTokenView

namespace Fang.Source.Grammar

/-- A nonempty comma-separated prefix; the closing parenthesis is not consumed. -/
inductive TermsPrefix : List Token → List Term → List Token → Prop where
  | last {input rest term} (head : TermTokens input term rest)
      (noComma : rest.head? ≠ some .comma) : TermsPrefix input [term] rest
  | more {input middle rest term terms}
      (head : TermTokens input term (.comma :: middle))
      (tail : TermsPrefix middle terms rest) : TermsPrefix input (term :: terms) rest

theorem TermsPrefix.arguments {input terms rest}
    (parsed : TermsPrefix input terms (.rparen :: rest)) : ArgumentsTokens input terms rest := by
  generalize ending : Source.Grammar.Token.rparen :: rest = output at parsed
  induction parsed with
  | last head noComma => exact .last (ending ▸ head)
  | more head tail induction => exact .more head (induction ending)

end Fang.Source.Grammar

namespace Fang.Frontend

open Source.Grammar

def TermGrammarResult (before : State) (tokens : List Source.Grammar.Token)
    (encoded : Fang.Term) (after : State) : Prop :=
  ∃ named rest, TableTermEncoding after named encoded ∧ TableExtension before after ∧
    TermTokens tokens named rest ∧ ClassifiedTokens after.tokens rest

def TermsGrammarResult (before : State) (tokens : List Source.Grammar.Token)
    (encoded : List Fang.Term) (after : State) : Prop :=
  ∃ named rest, TableTermsEncoding after named encoded ∧ TableExtension before after ∧
    TermsPrefix tokens named rest ∧ ClassifiedTokens after.tokens rest

theorem function_arguments_grammar (fuel : Nat) (reserved : State)
    (tokens : List Source.Grammar.Token) (name : String)
    (classified : ClassifiedTokens reserved.tokens tokens)
    (argumentsProof : ∀ {state tokens encoded updated}, ClassifiedTokens state.tokens tokens →
      terms fuel state = .ok (encoded, updated) → TermsGrammarResult state tokens encoded updated)
    {encoded : List Fang.Term} {updated : State}
    (success : (if reserved.tokens.head?.map Token.text == some "(" then do
      let (_, opened) ← expect "(" reserved
      let (args, afterArgs) ← terms fuel opened
      let (_, closed) ← expect ")" afterArgs
      pure (args, closed)
    else .ok ([], reserved)) = .ok (encoded, updated)) :
    ∃ named rest, TableTermsEncoding updated named encoded ∧ TableExtension reserved updated ∧
      TermTokens (.lower name :: tokens) (.app name named) rest ∧
      ClassifiedTokens updated.tokens rest := by
  split at success
  · cases openedRun : expect "(" reserved with
    | error error => simp [openedRun, bind, Except.bind] at success
    | ok pair =>
        rcases pair with ⟨returnedUnit, opened⟩
        cases returnedUnit
        obtain ⟨inner, tokenShape, openClass⟩ := expect_punctuation (character := '(') openedRun classified
          (by simp [RawPunctuation]) .lparen .lparen
        cases argsRun : terms fuel opened with
        | error error => simp [openedRun, argsRun, bind, Except.bind] at success
        | ok pair =>
            rcases pair with ⟨args, afterArgs⟩
            cases closedRun : expect ")" afterArgs with
            | error error => simp [openedRun, argsRun, closedRun, bind, Except.bind] at success
            | ok pair =>
                rcases pair with ⟨returnedUnit, closed⟩
                cases returnedUnit
                simp [openedRun, argsRun, closedRun, bind, Except.bind, pure, Except.pure] at success
                rcases success with ⟨rfl, rfl⟩
                obtain ⟨named, middle, encoding, extension, grammar, midClass⟩ := argumentsProof openClass argsRun
                obtain ⟨rest, middleShape, finalClass⟩ := expect_punctuation (character := ')') closedRun midClass
                  (by simp [RawPunctuation]) .rparen .rparen
                have closeExtension := expect_tableExtension closedRun
                refine ⟨named, rest, encoding.extend closeExtension,
                  (expect_tableExtension openedRun).trans (extension.trans closeExtension), ?_, finalClass⟩
                rw [tokenShape]
                exact .application name ((middleShape ▸ grammar).arguments)
  · rename_i noOpen
    cases success
    have noArguments : tokens.head? ≠ some .lparen := by
      intro same
      exact noOpen (by simpa only [beq_iff_eq] using classified.head_lparen.mpr same)
    exact ⟨[], tokens, .nil, .refl reserved, .constant name tokens noArguments, classified⟩

theorem term_function_grammar (fuel : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (notVariable : variableName token.text = false)
    (isFunction : lowerName token.text = true)
    {input : List Source.Grammar.Token} (classified : ClassifiedTokens state.tokens input)
    (argumentsProof : ∀ {state tokens encoded updated}, ClassifiedTokens state.tokens tokens →
      terms fuel state = .ok (encoded, updated) → TermsGrammarResult state tokens encoded updated)
    {encoded : Fang.Term} {updated : State}
    (success : term (fuel + 1) state = .ok (encoded, updated)) :
    TermGrammarResult state input encoded updated := by
  rw [tokens] at classified
  cases classified with
  | cons head tail =>
    have typedHead := head.is_lower isFunction
    subst typedHead
    obtain ⟨id, reserved, allocated, allocation, consumed, _⟩ :=
      reserveSymbol_spec false token.text { state with tokens := rest }
    rw [term_function_run fuel state reserved token rest id tokens notVariable isFunction allocated consumed] at success
    change reserved.tokens = rest at consumed
    rw [← consumed] at success
    cases argsRun : (if reserved.tokens.head?.map Token.text == some "(" then do
        let (_, opened) ← expect "(" reserved
        let (args, afterArgs) ← terms fuel opened
        let (_, closed) ← expect ")" afterArgs
        pure (args, closed)
      else .ok ([], reserved)) with
    | error error =>
        rw [argsRun] at success
        simp [Except.bind] at success
    | ok pair =>
        rcases pair with ⟨args, afterArgs⟩
        rw [argsRun] at success
        simp only [Except.bind] at success
        cases arityRun : checkArity false id args.length token.offset afterArgs with
        | error error => simp [arityRun, bind, Except.bind] at success
        | ok pair =>
            rcases pair with ⟨returnedUnit, final⟩
            cases returnedUnit
            simp [arityRun, bind, Except.bind, pure, Except.pure] at success
            rcases success with ⟨rfl, rfl⟩
            have reservedClass := consumed ▸ tail
            obtain ⟨named, ending, encoding, extension, grammar, finalClass⟩ :=
              function_arguments_grammar fuel reserved _ token.text reservedClass argumentsProof argsRun
            have arityExtension := checkArity_tableExtension false id args.length token.offset afterArgs final arityRun
            have allocationExtension := reserveSymbol_tableExtension false token.text _ reserved id allocated
            have reservedId : symbolIndex token.text reserved.functions 0 = some id := by
              rw [symbolIndex_eq_namedIndex]
              exact (namedIndex_first_iff _ _ _).mpr allocation.1
            have finalId := arityExtension.symbols false token.text id (extension.symbols false token.text id reservedId)
            have contract := checkArity_success false id args.length token.offset afterArgs final arityRun
            have namedArity : (final.functions[id]?).map Symbol.arity = some (some named.length) := by
              simpa only [encoding.length, symbolTable, Bool.false_eq_true, ↓reduceIte] using contract.1
            have initialExtension : TableExtension state { state with tokens := rest } :=
              tableExtension_of_same_tables rfl rfl rfl
            exact ⟨.app token.text named, ending,
              .app token.text id named args finalId namedArity (encoding.extend arityExtension),
              initialExtension.trans (allocationExtension.trans (extension.trans arityExtension)),
              grammar, contract.2.2.1 ▸ finalClass⟩

theorem term_variable_grammar (fuel : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (isVariable : variableName token.text = true)
    {input : List Source.Grammar.Token} (classified : ClassifiedTokens state.tokens input)
    {encoded : Fang.Term} {updated : State}
    (success : term (fuel + 1) state = .ok (encoded, updated)) :
    TermGrammarResult state input encoded updated := by
  rw [tokens] at classified
  cases classified with
  | cons head tail =>
    have typedHead := head.is_variable isVariable
    subst typedHead
    rw [term_variable_run fuel state token rest tokens isVariable] at success
    obtain ⟨id, final, allocated, allocation, consumed, _⟩ :=
      variableId_spec token.text { state with tokens := rest }
    simp [allocated, bind, Except.bind, pure, Except.pure] at success
    rcases success with ⟨rfl, rfl⟩
    have found := (namedIndex_first_iff token.text final.variables id).mpr allocation.1
    have initialExtension : TableExtension state { state with tokens := rest } :=
      tableExtension_of_same_tables rfl rfl rfl
    exact ⟨.var token.text, _, .var token.text id found,
      initialExtension.trans (variableId_tableExtension token.text _ final id allocated),
      .variableTerm token.text _, consumed ▸ tail⟩

theorem terms_success_grammar (fuel : Nat) (state : State)
    (termProof : ∀ {state tokens encoded updated}, ClassifiedTokens state.tokens tokens →
      term fuel state = .ok (encoded, updated) → TermGrammarResult state tokens encoded updated)
    (termsProof : ∀ {state tokens encoded updated}, ClassifiedTokens state.tokens tokens →
      terms fuel state = .ok (encoded, updated) → TermsGrammarResult state tokens encoded updated)
    {input : List Source.Grammar.Token} (classified : ClassifiedTokens state.tokens input)
    {encoded : List Fang.Term} {updated : State}
    (success : terms (fuel + 1) state = .ok (encoded, updated)) :
    TermsGrammarResult state input encoded updated := by
  rw [terms_run] at success
  cases firstRun : term fuel state with
  | error error => simp [firstRun, bind, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨first, afterFirst⟩
      simp only [firstRun, bind, Except.bind] at success
      obtain ⟨namedFirst, middle, firstEncoding, firstExtension, firstGrammar, middleClass⟩ :=
        termProof classified firstRun
      split at success
      · cases commaRun : expect "," afterFirst with
        | error error => simp [commaRun] at success
        | ok pair =>
            rcases pair with ⟨returnedUnit, afterComma⟩
            cases returnedUnit
            obtain ⟨afterTokens, middleShape, commaClass⟩ := expect_punctuation (character := ',') commaRun middleClass
              (by simp [RawPunctuation]) .comma .comma
            cases tailRun : terms fuel afterComma with
            | error error => simp [commaRun, tailRun] at success
            | ok pair =>
                rcases pair with ⟨tail, final⟩
                simp [commaRun, tailRun, pure, Except.pure] at success
                rcases success with ⟨rfl, rfl⟩
                obtain ⟨namedTail, ending, tailEncoding, tailExtension, tailGrammar, finalClass⟩ :=
                  termsProof commaClass tailRun
                have extension := (expect_tableExtension commaRun).trans tailExtension
                exact ⟨namedFirst :: namedTail, ending,
                  .cons (firstEncoding.extend extension) tailEncoding,
                  firstExtension.trans extension, .more (middleShape ▸ firstGrammar) tailGrammar, finalClass⟩
      · rename_i noComma
        cases success
        have noCommaToken : middle.head? ≠ some .comma := by
          intro same
          exact noComma (by simpa only [beq_iff_eq] using middleClass.head_comma.mpr same)
        exact ⟨[namedFirst], middle, .cons firstEncoding .nil, firstExtension,
          .last firstGrammar noCommaToken, middleClass⟩

theorem term_terms_grammar (fuel : Nat) :
    (∀ {state tokens encoded updated}, ClassifiedTokens state.tokens tokens →
      term fuel state = .ok (encoded, updated) → TermGrammarResult state tokens encoded updated) ∧
    (∀ {state tokens encoded updated}, ClassifiedTokens state.tokens tokens →
      terms fuel state = .ok (encoded, updated) → TermsGrammarResult state tokens encoded updated) := by
  induction fuel with
  | zero =>
      constructor <;> intro state tokens encoded updated classified success
      · simp [term, fail_run] at success
      · simp [terms, fail_run] at success
  | succ fuel induction =>
      constructor
      · intro state input encoded updated classified success
        cases tokens : state.tokens with
        | nil =>
            simp [term, position, consume, tokens, fail_run, bind, pure, get, getThe,
              MonadStateOf.get, StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind] at success
        | cons token rest =>
            cases isVariable : variableName token.text with
            | true => exact term_variable_grammar fuel state token rest tokens isVariable classified success
            | false =>
                cases isFunction : lowerName token.text with
                | true => exact term_function_grammar fuel state token rest tokens isVariable isFunction classified induction.2 success
                | false =>
                    simp [term, position, consume, tokens, isVariable, isFunction,
                      failAt_run, bind, pure, get, getThe, MonadStateOf.get, set,
                      StateT.bind, StateT.get, StateT.pure, StateT.set, Except.pure, Except.bind] at success
      · intro state input encoded updated classified success
        exact terms_success_grammar fuel state induction.1 induction.2 classified success

theorem term_grammar {fuel state tokens encoded updated}
    (classified : ClassifiedTokens state.tokens tokens)
    (success : term fuel state = .ok (encoded, updated)) :
    TermGrammarResult state tokens encoded updated := (term_terms_grammar fuel).1 classified success

theorem terms_grammar {fuel state tokens encoded updated}
    (classified : ClassifiedTokens state.tokens tokens)
    (success : terms fuel state = .ok (encoded, updated)) :
    TermsGrammarResult state tokens encoded updated := (term_terms_grammar fuel).2 classified success

#print axioms function_arguments_grammar
#print axioms term_grammar
#print axioms terms_grammar

end Fang.Frontend
