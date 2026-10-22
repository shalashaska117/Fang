/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Arity updates and rejection in the actual independent decoder.
-/
import Fang.FrontendNames
import Fang.FrontendParser

namespace Fang.Frontend

def symbolTable (state : State) (predicate : Bool) : List Symbol :=
  if predicate then state.predicates else state.functions

def replaceSymbolTable (state : State) (predicate : Bool) (symbols : List Symbol) : State :=
  if predicate then { state with predicates := symbols }
  else { state with functions := symbols }

theorem checkArity_run (predicate : Bool) (id arity offset : Nat) (state : State) :
    checkArity predicate id arity offset state =
      match (symbolTable state predicate)[id]? with
      | none => fail "invalid-syntax: missing symbol" state
      | some symbol =>
        match symbol.arity with
        | some previous =>
          if previous != arity then
            failAt offset s!"invalid-syntax: inconsistent arity for '{symbol.name}'" state
          else .ok ((), state)
        | none => .ok ((), replaceSymbolTable state predicate
            ((symbolTable state predicate).set id { symbol with arity := some arity })) := by
  cases found : (symbolTable state predicate)[id]? with
  | none =>
    cases predicate <;>
      simp_all [checkArity, symbolTable, bind, pure, get, getThe, MonadStateOf.get,
        StateT.bind, StateT.get, Except.pure, Except.bind]
  | some symbol =>
    cases previous : symbol.arity with
    | none =>
      cases predicate <;>
        simp_all [checkArity, symbolTable, replaceSymbolTable, bind, pure, get, getThe,
          MonadStateOf.get, set, StateT.bind, StateT.get, StateT.set,
          Except.pure, Except.bind]
    | some previousArity =>
      cases predicate <;> by_cases same : previousArity = arity <;>
        simp_all [checkArity, symbolTable, bind, pure, get, getThe, MonadStateOf.get,
          StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind]

theorem symbol_names_set_arity (symbols : List Symbol) (id arity : Nat) (symbol : Symbol)
    (found : symbols[id]? = some symbol) :
    (symbols.set id { symbol with arity := some arity }).map Symbol.name =
      symbols.map Symbol.name := by
  induction symbols generalizing id with
  | nil => simp at found
  | cons head tail ih =>
    cases id with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst head
      rfl
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      simpa only [List.set_cons_succ, List.map_cons] using
        congrArg (head.name :: ·) (ih index found)

def ArityChecked (predicate : Bool) (id arity : Nat) (before after : State) : Prop :=
  ((symbolTable after predicate)[id]?).map Symbol.arity = some (some arity) ∧
  selectedSymbolNames after predicate = selectedSymbolNames before predicate ∧
  after.tokens = before.tokens ∧ after.endOffset = before.endOffset ∧
  after.variables = before.variables ∧ after.clauseNames = before.clauseNames ∧
  symbolTable after (!predicate) = symbolTable before (!predicate)

theorem arityChecked_existing (predicate : Bool) (id arity : Nat) (state : State)
    (symbol : Symbol) (found : (symbolTable state predicate)[id]? = some symbol)
    (same : symbol.arity = some arity) : ArityChecked predicate id arity state state := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  simp [found, same]

theorem arityChecked_updated (predicate : Bool) (id arity : Nat) (state : State)
    (symbol : Symbol) (found : (symbolTable state predicate)[id]? = some symbol) :
    ArityChecked predicate id arity state (replaceSymbolTable state predicate
      ((symbolTable state predicate).set id { symbol with arity := some arity })) := by
  have within : id < (symbolTable state predicate).length :=
    List.getElem?_eq_some_iff.mp found |>.1
  have names := symbol_names_set_arity (symbolTable state predicate) id arity symbol found
  have updatedArity :
      (((symbolTable state predicate).set id { symbol with arity := some arity })[id]?).map
        Symbol.arity = some (some arity) := by
    rw [List.getElem?_set_self within]
    rfl
  cases predicate <;>
    simpa [ArityChecked, symbolTable, replaceSymbolTable, selectedSymbolNames] using
      And.intro updatedArity names

theorem checkArity_success (predicate : Bool) (id arity offset : Nat)
    (state updated : State) (returned : checkArity predicate id arity offset state = .ok ((), updated)) :
    ArityChecked predicate id arity state updated := by
  rw [checkArity_run] at returned
  cases found : (symbolTable state predicate)[id]? with
  | none => simp [found, fail_run] at returned
  | some symbol =>
    rw [found] at returned
    cases previous : symbol.arity with
    | none =>
      simp only [previous] at returned
      cases returned
      exact arityChecked_updated predicate id arity state symbol found
    | some previousArity =>
      simp only [previous] at returned
      by_cases same : previousArity = arity
      · simp only [same, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at returned
        cases returned
        exact arityChecked_existing predicate id arity state symbol found (same ▸ previous)
      · simp [same, failAt_run] at returned

theorem checkArity_rejects_mismatch (predicate : Bool) (id arity offset : Nat) (state : State)
    (symbol : Symbol) (previous : Nat)
    (found : (symbolTable state predicate)[id]? = some symbol)
    (declared : symbol.arity = some previous) (different : previous ≠ arity) :
    checkArity predicate id arity offset state =
      .error s!"invalid-syntax: inconsistent arity for '{symbol.name}' at byte {offset}" := by
  simp [checkArity_run, found, declared, different, failAt_run, toString, String.append_assoc]

theorem checkArity_initializes (predicate : Bool) (id arity offset : Nat) (state : State)
    (symbol : Symbol) (found : (symbolTable state predicate)[id]? = some symbol)
    (unset : symbol.arity = none) :
    checkArity predicate id arity offset state =
      .ok ((), replaceSymbolTable state predicate
        ((symbolTable state predicate).set id { symbol with arity := some arity })) := by
  simp [checkArity_run, found, unset]

theorem checkArity_accepts_consistent (predicate : Bool) (id arity offset : Nat) (state : State)
    (symbol : Symbol) (found : (symbolTable state predicate)[id]? = some symbol)
    (declared : symbol.arity = some arity) :
    checkArity predicate id arity offset state = .ok ((), state) := by
  simp [checkArity_run, found, declared]

theorem ArityChecked.all_names {predicate : Bool} {id arity : Nat} {before after : State}
    (checked : ArityChecked predicate id arity before after) (query : Bool) :
    selectedSymbolNames after query = selectedSymbolNames before query := by
  rcases checked with ⟨_, selected, _, _, _, _, other⟩
  cases predicate <;> cases query <;>
    first
    | exact selected
    | exact congrArg (List.map Symbol.name) other

theorem checkArity_preserves_ids (predicate query : Bool) (id arity offset : Nat)
    (state updated : State) (returned : checkArity predicate id arity offset state = .ok ((), updated))
    (name : String) (start : Nat) :
    symbolIndex name (symbolTable updated query) start =
      symbolIndex name (symbolTable state query) start := by
  rw [symbolIndex_eq_namedIndex, symbolIndex_eq_namedIndex]
  change namedIndex name (selectedSymbolNames updated query) start =
    namedIndex name (selectedSymbolNames state query) start
  rw [(checkArity_success predicate id arity offset state updated returned).all_names query]

theorem checkArity_preserves_unique (predicate : Bool) (id arity offset : Nat)
    (state updated : State) (returned : checkArity predicate id arity offset state = .ok ((), updated))
    (unique : NamesUnique state) : NamesUnique updated := by
  have checked := checkArity_success predicate id arity offset state updated returned
  have functions := checked.all_names false
  have predicates := checked.all_names true
  rcases checked with ⟨_, _, _, _, variables, _, _⟩
  unfold NamesUnique at unique ⊢
  change (updated.functions.map Symbol.name) = state.functions.map Symbol.name at functions
  change (updated.predicates.map Symbol.name) = state.predicates.map Symbol.name at predicates
  rw [variables, functions, predicates]
  exact unique

end Fang.Frontend

#print axioms Fang.Frontend.checkArity_success
#print axioms Fang.Frontend.checkArity_rejects_mismatch
#print axioms Fang.Frontend.checkArity_initializes
#print axioms Fang.Frontend.checkArity_accepts_consistent
#print axioms Fang.Frontend.checkArity_preserves_ids
#print axioms Fang.Frontend.checkArity_preserves_unique
