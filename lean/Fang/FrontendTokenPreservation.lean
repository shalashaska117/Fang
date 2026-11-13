/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FrontendArity

namespace Fang.Frontend

theorem variableId_preserves_tokens (name : String) (state updated : State) (id : Nat)
    (returned : variableId name state = .ok (id, updated)) : updated.tokens = state.tokens := by
  obtain ⟨actualId, actualState, actualReturned, _, tokens, _⟩ := variableId_spec name state
  rw [returned] at actualReturned
  cases actualReturned
  exact tokens

theorem reserveSymbol_preserves_tokens (predicate : Bool) (name : String)
    (state updated : State) (id : Nat)
    (returned : reserveSymbol predicate name state = .ok (id, updated)) :
    updated.tokens = state.tokens := by
  obtain ⟨actualId, actualState, actualReturned, _, tokens, _⟩ := reserveSymbol_spec predicate name state
  rw [returned] at actualReturned
  cases actualReturned
  exact tokens

theorem checkArity_preserves_tokens (predicate : Bool) (id arity offset : Nat)
    (state updated : State)
    (returned : checkArity predicate id arity offset state = .ok ((), updated)) :
    updated.tokens = state.tokens :=
  (checkArity_success predicate id arity offset state updated returned).2.2.1

end Fang.Frontend

#print axioms Fang.Frontend.variableId_preserves_tokens
#print axioms Fang.Frontend.reserveSymbol_preserves_tokens
#print axioms Fang.Frontend.checkArity_preserves_tokens
