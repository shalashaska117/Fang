/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Exact branch equations used to prove the existing recursive term parser.
No new production parser is defined here.
-/
import Fang.FrontendTerms
import Fang.FrontendTableEncoding

namespace Fang.Frontend

theorem consume_tableExtension {state updated : State} {name : String}
    (success : consume state = .ok (name, updated)) : TableExtension state updated := by
  obtain ⟨token, rest, _, _, rfl⟩ := consume_success success
  exact tableExtension_of_same_tables rfl rfl rfl

theorem expect_tableExtension {state updated : State} {wanted : String}
    (success : expect wanted state = .ok ((), updated)) : TableExtension state updated := by
  obtain ⟨token, rest, _, _, rfl⟩ := expect_success success
  exact tableExtension_of_same_tables rfl rfl rfl

theorem term_function_run (fuel : Nat) (state reserved : State) (token : Token)
    (rest : List Token) (id : Nat)
    (tokens : state.tokens = token :: rest) (notVariable : variableName token.text = false)
    (isFunction : lowerName token.text = true)
    (allocated : reserveSymbol false token.text { state with tokens := rest } = .ok (id, reserved))
    (reservedTokens : reserved.tokens = rest) :
    term (fuel + 1) state = Except.bind
      (if rest.head?.map Token.text == some "(" then do
          let (_, opened) ← expect "(" reserved
          let (args, afterArgs) ← terms fuel opened
          let (_, closed) ← expect ")" afterArgs
          pure (args, closed)
        else .ok ([], reserved))
      (fun (args, beforeArity) => do
        let (_, updated) ← checkArity false id args.length token.offset beforeArity
        pure (Fang.Term.app id args, updated)) := by
  simp [term, position, consume, peek, tokens, notVariable, isFunction,
    allocated, reservedTokens, bind, pure, get, getThe, MonadStateOf.get, set,
    StateT.bind, StateT.get, StateT.pure, StateT.set, Except.pure, Except.bind]
  split
  · simp only [StateT.bind, StateT.pure, bind, pure, Except.bind, Except.pure]
    repeat' first | split | rfl
    all_goals simp_all
  · rfl

theorem terms_run (fuel : Nat) (state : State) :
    terms (fuel + 1) state = (do
      let (first, afterFirst) ← term fuel state
      if afterFirst.tokens.head?.map Token.text == some "," then do
        let (_, consumed) ← expect "," afterFirst
        let (rest, updated) ← terms fuel consumed
        pure (first :: rest, updated)
      else .ok ([first], afterFirst)) := by
  simp only [terms, peek, bind, pure, get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind]
  cases result : term fuel state with
  | error error => rfl
  | ok pair =>
      dsimp only
      split <;> rfl

#print axioms consume_tableExtension
#print axioms expect_tableExtension
#print axioms term_function_run
#print axioms terms_run

end Fang.Frontend
