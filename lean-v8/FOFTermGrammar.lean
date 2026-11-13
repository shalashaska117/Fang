/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import FOFGrammar
import Fang.FrontendTermGrammar

namespace Fang.FOFFrontend
open Frontend FOFGrammar

def spellings (state : State) : List String := state.tokens.map Token.text

theorem spellings_head (state : State) :
    (spellings state).head? = state.tokens.head?.map Token.text := by
  simp [spellings]

theorem expect_spellings {state updated : State} {wanted : String}
    (success : expect wanted state = .ok ((), updated)) :
    spellings state = wanted :: spellings updated := by
  obtain ⟨token, rest, shape, text, rfl⟩ := expect_success success
  simp [spellings, shape, text]

theorem consume_spellings {state updated : State} {text : String}
    (success : consume state = .ok (text, updated)) :
    spellings state = text :: spellings updated := by
  obtain ⟨token, rest, shape, text, rfl⟩ := consume_success success
  simp [spellings, shape, text]

def RawTermResult (before : State) (encoded : Fang.Term) (after : State) : Prop :=
  ∃ named, TableTermEncoding after named encoded ∧ TableExtension before after ∧
    FOFGrammar.TermTokens (spellings before) named (spellings after)

def RawTermsResult (before : State) (encoded : List Fang.Term) (after : State) : Prop :=
  ∃ named, TableTermsEncoding after named encoded ∧ TableExtension before after ∧
    FOFGrammar.TermsPrefix (spellings before) named (spellings after)

theorem raw_function_arguments (fuel : Nat) (reserved : State) (name : String)
    (valid : Source.Grammar.LowerName name)
    (argumentsProof : ∀ {state encoded updated},
      terms fuel state = .ok (encoded, updated) → RawTermsResult state encoded updated)
    {encoded : List Fang.Term} {updated : State}
    (success : (if reserved.tokens.head?.map Token.text == some "(" then do
      let (_, opened) ← expect "(" reserved
      let (args, afterArgs) ← terms fuel opened
      let (_, closed) ← expect ")" afterArgs
      pure (args, closed)
    else .ok ([], reserved)) = .ok (encoded, updated)) :
    ∃ named, TableTermsEncoding updated named encoded ∧ TableExtension reserved updated ∧
      FOFGrammar.TermTokens (name :: spellings reserved) (.app name named) (spellings updated) := by
  split at success
  · cases openedRun : expect "(" reserved with
    | error error => simp [openedRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨ignored, opened⟩
      cases ignored
      cases argsRun : terms fuel opened with
      | error error => simp [openedRun, argsRun, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨args, afterArgs⟩
        cases closedRun : expect ")" afterArgs with
        | error error => simp [openedRun, argsRun, closedRun, bind, Except.bind] at success
        | ok pair =>
          rcases pair with ⟨ignored, closed⟩
          cases ignored
          simp [openedRun, argsRun, closedRun, bind, Except.bind, pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          obtain ⟨named, encoding, extension, grammar⟩ := argumentsProof argsRun
          have closeExtension := expect_tableExtension closedRun
          refine ⟨named, encoding.extend closeExtension,
            (expect_tableExtension openedRun).trans (extension.trans closeExtension), ?_⟩
          rw [expect_spellings openedRun]
          rw [expect_spellings closedRun] at grammar
          exact .application name valid grammar.arguments
  · rename_i noOpen
    cases success
    have noArguments : (spellings reserved).head? ≠ some "(" := by
      rw [spellings_head]
      simpa only [beq_iff_eq] using noOpen
    exact ⟨[], .nil, .refl reserved, .constant name _ valid noArguments⟩

theorem raw_term_function (fuel : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (notVariable : variableName token.text = false)
    (isFunction : lowerName token.text = true)
    (argumentsProof : ∀ {state encoded updated}, terms fuel state = .ok (encoded, updated) →
      RawTermsResult state encoded updated)
    {encoded : Fang.Term} {updated : State}
    (success : term (fuel + 1) state = .ok (encoded, updated)) :
    RawTermResult state encoded updated := by
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
  | error error => rw [argsRun] at success; simp [Except.bind] at success
  | ok pair =>
    rcases pair with ⟨args, afterArgs⟩
    rw [argsRun] at success
    simp only [Except.bind] at success
    cases arityRun : checkArity false id args.length token.offset afterArgs with
    | error error => simp [arityRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨ignored, final⟩
      cases ignored
      simp [arityRun, bind, Except.bind, pure, Except.pure] at success
      rcases success with ⟨rfl, rfl⟩
      have valid := (lowerName_iff token.text (lowerName_ascii isFunction)).mp isFunction
      obtain ⟨named, encoding, extension, grammar⟩ :=
        raw_function_arguments fuel reserved token.text valid argumentsProof argsRun
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
      refine ⟨.app token.text named,
        .app token.text id named args finalId namedArity (encoding.extend arityExtension),
        initialExtension.trans (allocationExtension.trans (extension.trans arityExtension)), ?_⟩
      simpa only [spellings, tokens, List.map_cons, consumed, contract.2.2.1] using grammar

theorem raw_term_variable (fuel : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (isVariable : variableName token.text = true)
    {encoded : Fang.Term} {updated : State}
    (success : term (fuel + 1) state = .ok (encoded, updated)) :
    RawTermResult state encoded updated := by
  rw [term_variable_run fuel state token rest tokens isVariable] at success
  obtain ⟨id, final, allocated, allocation, consumed, _⟩ :=
    variableId_spec token.text { state with tokens := rest }
  simp [allocated, bind, Except.bind, pure, Except.pure] at success
  rcases success with ⟨rfl, rfl⟩
  have found := (namedIndex_first_iff token.text final.variables id).mpr allocation.1
  have initialExtension : TableExtension state { state with tokens := rest } :=
    tableExtension_of_same_tables rfl rfl rfl
  refine ⟨.var token.text, .var token.text id found,
    initialExtension.trans (variableId_tableExtension token.text _ final id allocated), ?_⟩
  have grammar := FOFGrammar.TermTokens.variableTerm token.text (rest.map Token.text)
    ((variableName_iff token.text (variableName_ascii isVariable)).mp isVariable)
  simpa only [spellings, tokens, List.map_cons, consumed] using grammar

theorem raw_terms_step (fuel : Nat) (state : State)
    (termProof : ∀ {state encoded updated}, term fuel state = .ok (encoded, updated) →
      RawTermResult state encoded updated)
    (termsProof : ∀ {state encoded updated}, terms fuel state = .ok (encoded, updated) →
      RawTermsResult state encoded updated)
    {encoded : List Fang.Term} {updated : State}
    (success : terms (fuel + 1) state = .ok (encoded, updated)) :
    RawTermsResult state encoded updated := by
  rw [terms_run] at success
  cases firstRun : term fuel state with
  | error error => simp [firstRun, bind, Except.bind] at success
  | ok pair =>
    rcases pair with ⟨first, afterFirst⟩
    simp only [firstRun, bind, Except.bind] at success
    obtain ⟨namedFirst, firstEncoding, firstExtension, firstGrammar⟩ := termProof firstRun
    split at success
    · cases commaRun : expect "," afterFirst with
      | error error => simp [commaRun] at success
      | ok pair =>
        rcases pair with ⟨ignored, afterComma⟩
        cases ignored
        cases tailRun : terms fuel afterComma with
        | error error => simp [commaRun, tailRun] at success
        | ok pair =>
          rcases pair with ⟨tail, final⟩
          simp [commaRun, tailRun, pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          obtain ⟨namedTail, tailEncoding, tailExtension, tailGrammar⟩ := termsProof tailRun
          have extension := (expect_tableExtension commaRun).trans tailExtension
          rw [expect_spellings commaRun] at firstGrammar
          exact ⟨namedFirst :: namedTail, .cons (firstEncoding.extend extension) tailEncoding,
            firstExtension.trans extension, .more firstGrammar tailGrammar⟩
    · rename_i noComma
      cases success
      have noCommaToken : (spellings updated).head? ≠ some "," := by
        rw [spellings_head]
        simpa only [beq_iff_eq] using noComma
      exact ⟨[namedFirst], .cons firstEncoding .nil, firstExtension, .last firstGrammar noCommaToken⟩

theorem raw_term_terms_grammar (fuel : Nat) :
    (∀ {state encoded updated}, term fuel state = .ok (encoded, updated) → RawTermResult state encoded updated) ∧
    (∀ {state encoded updated}, terms fuel state = .ok (encoded, updated) → RawTermsResult state encoded updated) := by
  induction fuel with
  | zero =>
    constructor <;> intro state encoded updated success
    · simp [term, fail_run] at success
    · simp [terms, fail_run] at success
  | succ fuel ih =>
    constructor
    · intro state encoded updated success
      cases tokens : state.tokens with
      | nil =>
        simp [term, position, consume, tokens, fail_run, bind, pure, get, getThe,
          MonadStateOf.get, StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind] at success
      | cons token rest =>
        cases isVariable : variableName token.text with
        | true => exact raw_term_variable fuel state token rest tokens isVariable success
        | false =>
          cases isFunction : lowerName token.text with
          | true => exact raw_term_function fuel state token rest tokens isVariable isFunction ih.2 success
          | false =>
            simp [term, position, consume, tokens, isVariable, isFunction, failAt_run,
              bind, pure, get, getThe, MonadStateOf.get, set, StateT.bind, StateT.get,
              StateT.pure, StateT.set, Except.pure, Except.bind] at success
    · intro state encoded updated success
      exact raw_terms_step fuel state ih.1 ih.2 success

theorem raw_term_grammar {fuel state encoded updated}
    (success : term fuel state = .ok (encoded, updated)) : RawTermResult state encoded updated :=
  (raw_term_terms_grammar fuel).1 success

theorem raw_terms_grammar {fuel state encoded updated}
    (success : terms fuel state = .ok (encoded, updated)) : RawTermsResult state encoded updated :=
  (raw_term_terms_grammar fuel).2 success

end Fang.FOFFrontend
