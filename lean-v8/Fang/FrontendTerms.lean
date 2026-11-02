/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Base-case contracts for the existing term parser and semantic encoding.
The recursive application/argument correspondence is still a separate obligation.
-/
import Fang.FrontendEncoding

namespace Fang.Frontend

theorem term_variable_run (fuel : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (isVariable : variableName token.text = true) :
    term (fuel + 1) state = (do
      let (id, updated) ← variableId token.text { state with tokens := rest }
      pure (Fang.Term.var id, updated)) := by
  simp [term, position, consume, tokens, isVariable, bind, pure, get, getThe,
    MonadStateOf.get, set, StateT.bind, StateT.get, StateT.pure, StateT.set,
    Except.pure, Except.bind]

theorem term_variable_encoding {fuel : Nat} {state updated : State} {token : Token}
    {rest : List Token} {encoded : Fang.Term}
    (tokens : state.tokens = token :: rest) (isVariable : variableName token.text = true)
    (success : term (fuel + 1) state = .ok (encoded, updated)) :
    updated.tokens = rest ∧
    Source.TermEncoding (signatureFrom updated) (symbolsFrom updated)
      (variablesFrom updated.variables) (.var token.text) encoded := by
  rw [term_variable_run fuel state token rest tokens isVariable] at success
  obtain ⟨id, final, allocated, allocation, consumed, _⟩ :=
    variableId_spec token.text { state with tokens := rest }
  simp [allocated, bind, Except.bind, pure, Except.pure] at success
  rcases success with ⟨rfl, rfl⟩
  exact ⟨consumed, variableId_encoding token.text _ _ id allocated _ _⟩

theorem term_constant_run (fuel : Nat) (state : State) (token : Token) (rest : List Token)
    (tokens : state.tokens = token :: rest) (notVariable : variableName token.text = false)
    (isFunction : lowerName token.text = true)
    (notApplication : rest.head?.map Token.text ≠ some "(") :
    term (fuel + 1) state = (do
      let (id, reserved) ← reserveSymbol false token.text { state with tokens := rest }
      let ((), updated) ← checkArity false id 0 token.offset reserved
      pure (Fang.Term.app id [], updated)) := by
  cases found : symbolIndex token.text state.functions 0 <;>
    simp [term, position, consume, peek, reserveSymbol, tokens, notVariable, isFunction,
      notApplication, found, bind, pure, get, getThe, MonadStateOf.get, set,
      StateT.bind, StateT.get, StateT.pure, StateT.set, Except.pure, Except.bind]

theorem term_constant_encoding {fuel : Nat} {state updated : State} {token : Token}
    {rest : List Token} {encoded : Fang.Term}
    (tokens : state.tokens = token :: rest) (notVariable : variableName token.text = false)
    (isFunction : lowerName token.text = true)
    (notApplication : rest.head?.map Token.text ≠ some "(")
    (success : term (fuel + 1) state = .ok (encoded, updated)) :
    updated.tokens = rest ∧
    Source.TermEncoding (signatureFrom updated) (symbolsFrom updated)
      (variablesFrom updated.variables) (.app token.text []) encoded := by
  rw [term_constant_run fuel state token rest tokens notVariable isFunction notApplication] at success
  obtain ⟨id, reserved, allocated, allocation, consumed, _⟩ :=
    reserveSymbol_spec false token.text { state with tokens := rest }
  cases checked : checkArity false id 0 token.offset reserved with
  | error error => simp [allocated, checked, bind, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨returnedUnit, final⟩
      cases returnedUnit
      simp [allocated, checked, bind, Except.bind, pure, Except.pure] at success
      rcases success with ⟨rfl, rfl⟩
      have contract := checkArity_success false id 0 token.offset reserved final checked
      have reservedId : symbolIndex token.text reserved.functions 0 = some id := by
        rw [symbolIndex_eq_namedIndex]
        exact (namedIndex_first_iff token.text (reserved.functions.map Symbol.name) id).mpr allocation.1
      have finalId : symbolIndex token.text final.functions 0 = some id := by
        rw [← reservedId]
        exact checkArity_preserves_ids false false id 0 token.offset reserved final checked token.text 0
      refine ⟨contract.2.2.1.trans consumed, ?_⟩
      exact function_encoding_of_found final (variablesFrom final.variables) finalId contract.1 .nil

#print axioms term_variable_run
#print axioms term_variable_encoding
#print axioms term_constant_encoding

end Fang.Frontend
