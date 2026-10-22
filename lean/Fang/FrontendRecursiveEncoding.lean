/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Semantic table contracts for successful recursive term parsing.
Named syntax is constructed from the actual parser's consumed names. A separate
grammar correspondence theorem is still required to connect all source tokens.
-/
import Fang.FrontendTermRun

namespace Fang.Frontend

def TermResult (before : State) (encoded : Fang.Term) (after : State) : Prop :=
  ∃ named, TableTermEncoding after named encoded ∧ TableExtension before after

def TermsResult (before : State) (encoded : List Fang.Term) (after : State) : Prop :=
  ∃ named, TableTermsEncoding after named encoded ∧ TableExtension before after

theorem function_arguments_result (fuel : Nat) (reserved : State) (rest : List Token)
    (argumentsProof : ∀ {state encoded updated}, terms fuel state = .ok (encoded, updated) →
      TermsResult state encoded updated)
    {encoded : List Fang.Term} {updated : State}
    (success : (if rest.head?.map Token.text == some "(" then do
      let (_, opened) ← expect "(" reserved
      let (args, afterArgs) ← terms fuel opened
      let (_, closed) ← expect ")" afterArgs
      pure (args, closed)
    else .ok ([], reserved)) = .ok (encoded, updated)) :
    TermsResult reserved encoded updated := by
  split at success
  · cases openedRun : expect "(" reserved with
    | error error => simp [openedRun, bind, Except.bind] at success
    | ok pair =>
        rcases pair with ⟨returnedUnit, opened⟩
        cases returnedUnit
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
                obtain ⟨named, encoding, extension⟩ := argumentsProof argsRun
                have closeExtension := expect_tableExtension closedRun
                exact ⟨named, encoding.extend closeExtension,
                  (expect_tableExtension openedRun).trans (extension.trans closeExtension)⟩
  · cases success
    exact ⟨[], .nil, .refl reserved⟩

theorem term_function_result (fuel : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (notVariable : variableName token.text = false)
    (isFunction : lowerName token.text = true)
    (argumentsProof : ∀ {state encoded updated}, terms fuel state = .ok (encoded, updated) →
      TermsResult state encoded updated)
    {encoded : Fang.Term} {updated : State}
    (success : term (fuel + 1) state = .ok (encoded, updated)) :
    TermResult state encoded updated := by
  obtain ⟨id, reserved, allocated, allocation, consumed, _⟩ :=
    reserveSymbol_spec false token.text { state with tokens := rest }
  rw [term_function_run fuel state reserved token rest id tokens notVariable isFunction allocated consumed] at success
  cases argsRun : (if rest.head?.map Token.text == some "(" then do
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
      simp only [bind, Except.bind] at success
      cases arityRun : checkArity false id args.length token.offset afterArgs with
      | error error => simp [arityRun] at success
      | ok pair =>
          rcases pair with ⟨returnedUnit, final⟩
          cases returnedUnit
          simp [arityRun, pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          obtain ⟨named, encoding, extension⟩ := function_arguments_result fuel reserved rest argumentsProof argsRun
          have arityExtension := checkArity_tableExtension false id args.length token.offset afterArgs final arityRun
          have allocationExtension := reserveSymbol_tableExtension false token.text _ reserved id allocated
          have reservedId : symbolIndex token.text reserved.functions 0 = some id := by
            rw [symbolIndex_eq_namedIndex]
            exact (namedIndex_first_iff _ _ _).mpr allocation.1
          have finalId := arityExtension.symbols false token.text id (extension.symbols false token.text id reservedId)
          have arity := (checkArity_success false id args.length token.offset afterArgs final arityRun).1
          have namedArity : (final.functions[id]?).map Symbol.arity = some (some named.length) := by
            simpa only [encoding.length, symbolTable, Bool.false_eq_true, ↓reduceIte] using arity
          have initialExtension : TableExtension state { state with tokens := rest } :=
            tableExtension_of_same_tables rfl rfl rfl
          exact ⟨.app token.text named, .app token.text id named args finalId namedArity (encoding.extend arityExtension),
            initialExtension.trans
              (allocationExtension.trans (extension.trans arityExtension))⟩

theorem term_variable_result (fuel : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (isVariable : variableName token.text = true)
    {encoded : Fang.Term} {updated : State}
    (success : term (fuel + 1) state = .ok (encoded, updated)) :
    TermResult state encoded updated := by
  rw [term_variable_run fuel state token rest tokens isVariable] at success
  obtain ⟨id, final, allocated, allocation, _⟩ :=
    variableId_spec token.text { state with tokens := rest }
  simp [allocated, bind, Except.bind, pure, Except.pure] at success
  rcases success with ⟨rfl, rfl⟩
  have found := (namedIndex_first_iff token.text final.variables id).mpr allocation.1
  have initialExtension : TableExtension state { state with tokens := rest } :=
    tableExtension_of_same_tables rfl rfl rfl
  exact ⟨.var token.text, .var token.text id found,
    initialExtension.trans (variableId_tableExtension token.text _ final id allocated)⟩

theorem terms_success_result (fuel : Nat) (state : State)
    (termProof : ∀ {state encoded updated}, term fuel state = .ok (encoded, updated) →
      TermResult state encoded updated)
    (termsProof : ∀ {state encoded updated}, terms fuel state = .ok (encoded, updated) →
      TermsResult state encoded updated)
    {encoded : List Fang.Term} {updated : State}
    (success : terms (fuel + 1) state = .ok (encoded, updated)) :
    TermsResult state encoded updated := by
  rw [terms_run] at success
  cases firstRun : term fuel state with
  | error error => simp [firstRun, bind, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨first, afterFirst⟩
      simp only [firstRun, bind, Except.bind] at success
      obtain ⟨namedFirst, firstEncoding, firstExtension⟩ := termProof firstRun
      split at success
      · cases commaRun : expect "," afterFirst with
        | error error => simp [commaRun] at success
        | ok pair =>
            rcases pair with ⟨returnedUnit, afterComma⟩
            cases returnedUnit
            cases tailRun : terms fuel afterComma with
            | error error => simp [commaRun, tailRun] at success
            | ok pair =>
                rcases pair with ⟨tail, final⟩
                simp [commaRun, tailRun, pure, Except.pure] at success
                rcases success with ⟨rfl, rfl⟩
                obtain ⟨namedTail, tailEncoding, tailExtension⟩ := termsProof tailRun
                have extension := (expect_tableExtension commaRun).trans tailExtension
                exact ⟨namedFirst :: namedTail,
                  .cons (firstEncoding.extend extension) tailEncoding,
                  firstExtension.trans extension⟩
      · cases success
        exact ⟨[namedFirst], .cons firstEncoding .nil, firstExtension⟩

theorem term_terms_result (fuel : Nat) :
    (∀ {state encoded updated}, term fuel state = .ok (encoded, updated) →
      TermResult state encoded updated) ∧
    (∀ {state encoded updated}, terms fuel state = .ok (encoded, updated) →
      TermsResult state encoded updated) := by
  induction fuel with
  | zero =>
      constructor <;> intro state encoded updated success
      · simp [term, fail_run] at success
      · simp [terms, fail_run] at success
  | succ fuel induction =>
      constructor
      · intro state encoded updated success
        cases tokens : state.tokens with
        | nil =>
            simp [term, position, consume, tokens, fail_run, bind, pure, get, getThe,
              MonadStateOf.get, StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind] at success
        | cons token rest =>
            cases isVariable : variableName token.text with
            | true => exact term_variable_result fuel state token rest tokens isVariable success
            | false =>
                cases isFunction : lowerName token.text with
                | true => exact term_function_result fuel state token rest tokens isVariable isFunction induction.2 success
                | false =>
                    simp [term, position, consume, tokens, isVariable, isFunction,
                      failAt_run, bind, pure, get, getThe, MonadStateOf.get, set,
                      StateT.bind, StateT.get, StateT.pure, StateT.set, Except.pure, Except.bind] at success
      · intro state encoded updated success
        exact terms_success_result fuel state induction.1 induction.2 success

theorem term_result {fuel state encoded updated}
    (success : term fuel state = .ok (encoded, updated)) :
    TermResult state encoded updated := (term_terms_result fuel).1 success

theorem terms_result {fuel state encoded updated}
    (success : terms fuel state = .ok (encoded, updated)) :
    TermsResult state encoded updated := (term_terms_result fuel).2 success

#print axioms function_arguments_result
#print axioms term_function_result
#print axioms term_result
#print axioms terms_result

end Fang.Frontend
