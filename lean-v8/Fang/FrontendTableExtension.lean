/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Existing names and known arities survive successful parser table updates.
-/
import Fang.FrontendArity

namespace Fang.Frontend

structure TableExtension (before after : State) : Prop where
  variables : ∀ name id, namedIndex name before.variables 0 = some id →
    namedIndex name after.variables 0 = some id
  symbols : ∀ predicate name id,
    symbolIndex name (symbolTable before predicate) 0 = some id →
    symbolIndex name (symbolTable after predicate) 0 = some id
  arities : ∀ (predicate : Bool) (id arity : Nat),
    ((symbolTable before predicate)[id]?).map Symbol.arity = some (some arity) →
    ((symbolTable after predicate)[id]?).map Symbol.arity = some (some arity)

theorem TableExtension.refl (state : State) : TableExtension state state :=
  ⟨fun _ _ found => found, fun _ _ _ found => found, fun _ _ _ found => found⟩

theorem TableExtension.trans {first second third : State}
    (left : TableExtension first second) (right : TableExtension second third) :
    TableExtension first third :=
  ⟨fun name id found => right.variables name id (left.variables name id found),
   fun predicate name id found => right.symbols predicate name id
     (left.symbols predicate name id found),
   fun predicate id arity found => right.arities predicate id arity
     (left.arities predicate id arity found)⟩

theorem tableExtension_of_same_tables {before after : State}
    (variables : after.variables = before.variables)
    (functions : after.functions = before.functions)
    (predicates : after.predicates = before.predicates) : TableExtension before after := by
  constructor
  · intro name id found
    simpa only [variables] using found
  · intro predicate name id found
    simpa only [symbolTable, functions, predicates] using found
  · intro predicate id arity found
    simpa only [symbolTable, functions, predicates] using found

theorem variableId_tableExtension (name : String) (state updated : State) (id : Nat)
    (returned : variableId name state = .ok (id, updated)) : TableExtension state updated := by
  obtain ⟨actualId, actualState, actualReturned, allocation, _, _, functions, predicates, _⟩ :=
    variableId_spec name state
  rw [returned] at actualReturned
  cases actualReturned
  constructor
  · exact allocation.2.2.1
  · intro predicate other oldId found
    simpa only [symbolTable, functions, predicates] using found
  · intro predicate oldId arity found
    simpa only [symbolTable, functions, predicates] using found

theorem getElem?_append_preserves {α : Type} (before extra : List α) (id : Nat) (entry : α)
    (found : before[id]? = some entry) : (before ++ extra)[id]? = some entry := by
  have within := (List.getElem?_eq_some_iff.mp found).1
  simpa only [List.getElem?_append_left within] using found

theorem reserveSymbol_preserves_entry (predicate query : Bool) (name : String)
    (state updated : State) (id previousId : Nat) (entry : Symbol)
    (returned : reserveSymbol predicate name state = .ok (id, updated))
    (found : (symbolTable state query)[previousId]? = some entry) :
    (symbolTable updated query)[previousId]? = some entry := by
  rw [reserveSymbol_run] at returned
  cases predicate <;> simp only [Bool.false_eq_true, ↓reduceIte] at returned
  · cases existing : symbolIndex name state.functions 0 with
    | some existingId =>
      simp only [existing] at returned
      cases returned
      exact found
    | none =>
      simp only [existing] at returned
      cases returned
      cases query with
      | false => exact getElem?_append_preserves _ _ _ _ found
      | true => exact found
  · cases existing : symbolIndex name state.predicates 0 with
    | some existingId =>
      simp only [existing] at returned
      cases returned
      exact found
    | none =>
      simp only [existing] at returned
      cases returned
      cases query with
      | false => exact found
      | true => exact getElem?_append_preserves _ _ _ _ found

theorem reserveSymbol_tableExtension (predicate : Bool) (name : String)
    (state updated : State) (id : Nat)
    (returned : reserveSymbol predicate name state = .ok (id, updated)) :
    TableExtension state updated := by
  obtain ⟨actualId, actualState, actualReturned, allocation, _, _, variables, _, other⟩ :=
    reserveSymbol_spec predicate name state
  rw [returned] at actualReturned
  cases actualReturned
  constructor
  · intro name id found
    simpa only [variables] using found
  · intro query oldName oldId found
    have selected : ∀ oldName oldId,
        symbolIndex oldName (symbolTable state predicate) 0 = some oldId →
        symbolIndex oldName (symbolTable updated predicate) 0 = some oldId := by
      intro oldName oldId previous
      rw [symbolIndex_eq_namedIndex] at previous ⊢
      exact allocation.2.2.1 oldName oldId previous
    cases predicate <;> simp only [Bool.false_eq_true, ↓reduceIte] at other <;> cases query <;>
      first
      | exact selected _ _ found
      | simpa only [symbolTable, Bool.false_eq_true, ↓reduceIte, other] using found
  · intro query oldId arity found
    obtain ⟨entry, previous, known⟩ := Option.map_eq_some_iff.mp found
    have preserved := reserveSymbol_preserves_entry predicate query name state updated id
      oldId entry returned previous
    simp only [preserved, Option.map_some, known]

theorem set_unknown_arity_preserves_known (symbols : List Symbol) (id arity : Nat)
    (entry : Symbol) (found : symbols[id]? = some entry) (unknown : entry.arity = none)
    (oldId oldArity : Nat)
    (known : (symbols[oldId]?).map Symbol.arity = some (some oldArity)) :
    ((symbols.set id { entry with arity := some arity })[oldId]?).map Symbol.arity =
      some (some oldArity) := by
  by_cases same : oldId = id
  · subst oldId
    simp [found, unknown] at known
  · simpa only [List.getElem?_set_ne (Ne.symm same)] using known

theorem checkArity_preserves_known (predicate query : Bool) (id arity offset : Nat)
    (state updated : State)
    (returned : checkArity predicate id arity offset state = .ok ((), updated))
    (oldId oldArity : Nat)
    (known : ((symbolTable state query)[oldId]?).map Symbol.arity = some (some oldArity)) :
    ((symbolTable updated query)[oldId]?).map Symbol.arity = some (some oldArity) := by
  rw [checkArity_run] at returned
  cases found : (symbolTable state predicate)[id]? with
  | none => simp [found, fail_run] at returned
  | some entry =>
    rw [found] at returned
    cases previous : entry.arity with
    | some previousArity =>
      simp only [previous] at returned
      by_cases same : previousArity = arity
      · simp only [same, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at returned
        cases returned
        exact known
      · simp [same, failAt_run] at returned
    | none =>
      simp only [previous] at returned
      cases returned
      have selected := set_unknown_arity_preserves_known (symbolTable state predicate)
        id arity entry found previous oldId oldArity
      cases predicate <;> cases query <;>
        first
        | exact selected known
        | exact known

theorem checkArity_tableExtension (predicate : Bool) (id arity offset : Nat)
    (state updated : State)
    (returned : checkArity predicate id arity offset state = .ok ((), updated)) :
    TableExtension state updated := by
  have checked := checkArity_success predicate id arity offset state updated returned
  constructor
  · intro name oldId found
    simpa only [checked.2.2.2.2.1] using found
  · intro query name oldId found
    rw [checkArity_preserves_ids predicate query id arity offset state updated returned name 0]
    exact found
  · intro query oldId oldArity known
    exact checkArity_preserves_known predicate query id arity offset state updated returned
      oldId oldArity known

end Fang.Frontend

#print axioms Fang.Frontend.variableId_tableExtension
#print axioms Fang.Frontend.reserveSymbol_preserves_entry
#print axioms Fang.Frontend.reserveSymbol_tableExtension
#print axioms Fang.Frontend.checkArity_preserves_known
#print axioms Fang.Frontend.checkArity_tableExtension
