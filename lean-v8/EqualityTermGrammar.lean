/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   General successful named-term parsing correspondence. -/
import EqualitySourceInput
import EqualitySourceGrammar
import Fang.FrontendTokenView

namespace Fang.EqualityFrontend
open Frontend EqualitySource.Grammar

theorem parser_bind_success {α β : Type} {head : Parser α} {tail : α → Parser β}
    {state final : State} {value : β}
    (success : (head >>= tail) state = .ok (value, final)) :
    ∃ intermediate updated, head state = .ok (intermediate, updated) ∧
      tail intermediate updated = .ok (value, final) := by
  cases execution : head state with
  | error error => simp [bind, StateT.bind, execution, Except.bind] at success
  | ok pair =>
    rcases pair with ⟨intermediate, updated⟩
    exact ⟨intermediate, updated, rfl,
      by simpa [bind, StateT.bind, execution, Except.bind] using success⟩

def spellings (state : State) : List String := state.tokens.map Token.text

theorem spellings_head (state : State) :
    (spellings state).head? = state.tokens.head?.map Token.text := by simp [spellings]

theorem expect_spellings {state updated : State} {wanted : String}
    (success : expect wanted state = .ok ((), updated)) :
    spellings state = wanted :: spellings updated := by
  obtain ⟨token, rest, shape, text, rfl⟩ := expect_success success
  simp [spellings, shape, text]

theorem namedTerm_variable_run (fuel depth : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (isVariable : variableName token.text = true)
    (withinDepth : ¬ depth > 64) :
    namedTerm (fuel + 1) depth state = .ok (.var token.text, {state with tokens := rest}) := by
  simp [namedTerm, withinDepth, position, consume, tokens, isVariable, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.get, StateT.pure,
    StateT.set, Except.pure, Except.bind]

theorem namedTerm_function_run (fuel depth : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (notVariable : variableName token.text = false)
    (isFunction : lowerName token.text = true) (withinDepth : ¬ depth > 64) :
    namedTerm (fuel + 1) depth state = Except.bind
        (if rest.head?.map Token.text == some "(" then do
          let (_, opened) ← expect "(" {state with tokens := rest}
          let (arguments, afterArguments) ← namedTerms fuel (depth + 1) opened
          let (_, closed) ← expect ")" afterArguments
          pure (arguments, closed)
        else .ok ([], {state with tokens := rest}))
      (fun (arguments, afterArguments) => pure (.app token.text arguments, afterArguments)) := by
  simp [namedTerm, withinDepth, position, consume, tokens, notVariable, isFunction,
    peek, bind, pure, get, getThe, MonadStateOf.get, set, StateT.bind, StateT.get,
    StateT.pure, StateT.set, Except.pure, Except.bind]
  split
  · simp only [StateT.bind, StateT.pure, bind, pure, Except.bind, Except.pure]
    repeat' first | split | rfl
    all_goals simp_all
  · rfl

theorem namedTerms_run (fuel depth : Nat) (state : State) :
    namedTerms (fuel + 1) depth state = (do
      let (first, afterFirst) ← namedTerm fuel depth state
      if afterFirst.tokens.head?.map Token.text == some "," then do
        let (_, afterComma) ← expect "," afterFirst
        let (rest, final) ← namedTerms fuel depth afterComma
        pure (first :: rest, final)
      else .ok ([first], afterFirst)) := by
  simp only [namedTerms, peek, bind, pure, get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind]
  cases result : namedTerm fuel depth state with
  | error error => rfl
  | ok pair =>
    dsimp only
    split <;> rfl

theorem named_function_arguments (fuel depth : Nat) (state : State) (name : String)
    (valid : Source.Grammar.LowerName name)
    (childrenProof : ∀ {state terms updated}, namedTerms fuel depth state = .ok (terms, updated) →
      TermsPrefix (spellings state) terms (spellings updated))
    {arguments updated}
    (success : (if state.tokens.head?.map Token.text == some "(" then do
      let (_, opened) ← expect "(" state
      let (arguments, afterArguments) ← namedTerms fuel depth opened
      let (_, closed) ← expect ")" afterArguments
      pure (arguments, closed)
    else .ok ([], state)) = .ok (arguments, updated)) :
    TermTokens (name :: spellings state) (.app name arguments) (spellings updated) := by
  split at success
  · cases openedRun : expect "(" state with
    | error error => simp [openedRun, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨ignored, opened⟩
      cases ignored
      cases argumentsRun : namedTerms fuel depth opened with
      | error error => simp [openedRun, argumentsRun, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨terms, afterArguments⟩
        cases closedRun : expect ")" afterArguments with
        | error error => simp [openedRun, argumentsRun, closedRun, bind, Except.bind] at success
        | ok pair =>
          rcases pair with ⟨ignored, closed⟩
          cases ignored
          simp [openedRun, argumentsRun, closedRun, bind, Except.bind, pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          have grammar := childrenProof argumentsRun
          rw [expect_spellings openedRun]
          rw [expect_spellings closedRun] at grammar
          exact .application name valid grammar.arguments
  · rename_i noOpen
    cases success
    apply TermTokens.constant name _ valid
    rw [spellings_head]
    simpa only [beq_iff_eq] using noOpen

theorem named_terms_step (fuel depth : Nat) (state : State)
    (termProof : ∀ {state term updated}, namedTerm fuel depth state = .ok (term, updated) →
      TermTokens (spellings state) term (spellings updated))
    (termsProof : ∀ {state terms updated}, namedTerms fuel depth state = .ok (terms, updated) →
      TermsPrefix (spellings state) terms (spellings updated))
    {terms updated} (success : namedTerms (fuel + 1) depth state = .ok (terms, updated)) :
    TermsPrefix (spellings state) terms (spellings updated) := by
  rw [namedTerms_run] at success
  cases firstRun : namedTerm fuel depth state with
  | error error => simp [firstRun, bind, Except.bind] at success
  | ok pair =>
    rcases pair with ⟨first, afterFirst⟩
    simp only [firstRun, bind, Except.bind] at success
    have grammar := termProof firstRun
    split at success
    · cases commaRun : expect "," afterFirst with
      | error error => simp [commaRun] at success
      | ok pair =>
        rcases pair with ⟨ignored, afterComma⟩
        cases ignored
        cases tailRun : namedTerms fuel depth afterComma with
        | error error => simp [commaRun, tailRun] at success
        | ok pair =>
          rcases pair with ⟨tail, final⟩
          simp [commaRun, tailRun, pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          rw [expect_spellings commaRun] at grammar
          exact .more grammar (termsProof tailRun)
    · rename_i noComma
      cases success
      apply TermsPrefix.last grammar
      rw [spellings_head]
      simpa only [beq_iff_eq] using noComma

theorem named_term_terms_grammar (fuel : Nat) :
    (∀ {depth state term updated}, namedTerm fuel depth state = .ok (term, updated) →
      TermTokens (spellings state) term (spellings updated)) ∧
    (∀ {depth state terms updated}, namedTerms fuel depth state = .ok (terms, updated) →
      TermsPrefix (spellings state) terms (spellings updated)) := by
  induction fuel with
  | zero =>
    constructor <;> intro depth state term updated success
    · simp [namedTerm, fail_run] at success
    · simp [namedTerms, fail_run] at success
  | succ fuel ih =>
    constructor
    · intro depth state term updated success
      by_cases withinDepth : depth > 64
      · simp [namedTerm, withinDepth, fail_run, bind, StateT.bind, Except.bind] at success
      · cases tokens : state.tokens with
        | nil =>
          simp [namedTerm, withinDepth, position, consume, tokens, fail_run, bind, pure,
            get, getThe, MonadStateOf.get, StateT.bind, StateT.get, StateT.pure,
            Except.pure, Except.bind] at success
        | cons token rest =>
          cases isVariable : variableName token.text with
          | true =>
            rw [namedTerm_variable_run fuel depth state token rest tokens isVariable withinDepth] at success
            cases success
            simpa [spellings, tokens] using TermTokens.variableTerm token.text (rest.map Token.text)
              ((variableName_iff token.text (variableName_ascii isVariable)).mp isVariable)
          | false =>
            cases isFunction : lowerName token.text with
            | false =>
              simp [namedTerm, withinDepth, position, consume, tokens, isVariable, isFunction,
                failAt_run, bind, pure, get, getThe, MonadStateOf.get, set, StateT.bind,
                StateT.get, StateT.pure, StateT.set, Except.pure, Except.bind] at success
            | true =>
              rw [namedTerm_function_run fuel depth state token rest tokens isVariable isFunction withinDepth] at success
              cases argumentsRun : (if rest.head?.map Token.text == some "(" then do
                let (_, opened) ← expect "(" {state with tokens := rest}
                let (arguments, afterArguments) ← namedTerms fuel (depth + 1) opened
                let (_, closed) ← expect ")" afterArguments
                pure (arguments, closed)
              else .ok ([], {state with tokens := rest})) with
              | error error => rw [argumentsRun] at success; simp [Except.bind] at success
              | ok pair =>
                rcases pair with ⟨arguments, final⟩
                rw [argumentsRun] at success
                simp only [Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at success
                rcases success with ⟨rfl, rfl⟩
                have valid := (lowerName_iff token.text (lowerName_ascii isFunction)).mp isFunction
                have grammar := named_function_arguments fuel (depth + 1)
                  {state with tokens := rest} token.text valid ih.2 argumentsRun
                simpa [spellings, tokens] using grammar
    · intro depth state terms updated success
      exact named_terms_step fuel depth state ih.1 ih.2 success

theorem named_term_grammar {fuel depth state term updated}
    (success : namedTerm fuel depth state = .ok (term, updated)) :
    TermTokens (spellings state) term (spellings updated) := (named_term_terms_grammar fuel).1 success

theorem named_terms_grammar {fuel depth state terms updated}
    (success : namedTerms fuel depth state = .ok (terms, updated)) :
    TermsPrefix (spellings state) terms (spellings updated) := (named_term_terms_grammar fuel).2 success

end Fang.EqualityFrontend
