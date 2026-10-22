/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
First-occurrence name lookup in the actual independent input decoder.
This module does not prove the full decoder's grammar correspondence.
-/
import Fang.Input

namespace Fang.Frontend

def FirstNameAt (names : List String) (name : String) (index : Nat) : Prop :=
  ∃ within : index < names.length, names[index] = name ∧
    ∀ earlier (before : earlier < index), names[earlier]'(Nat.lt_trans before within) ≠ name

theorem namedIndex_eq_idxOf (name : String) (names : List String) (offset : Nat) :
    namedIndex name names offset = (names.idxOf? name).map (offset + ·) := by
  induction names generalizing offset with
  | nil => simp [namedIndex]
  | cons candidate rest ih =>
    by_cases same : name = candidate
    · subst candidate
      simp [namedIndex, List.idxOf?_cons]
    · simp [namedIndex, List.idxOf?_cons, same, Ne.symm same, ih,
        Option.map_map, Function.comp_def, Nat.add_comm, Nat.add_left_comm]

theorem namedIndex_some_iff (name : String) (names : List String) (offset id : Nat) :
    namedIndex name names offset = some id ↔
      ∃ relative, FirstNameAt names name relative ∧ offset + relative = id := by
  rw [namedIndex_eq_idxOf, Option.map_eq_some_iff]
  simp only [List.idxOf?_eq_some_iff, FirstNameAt]

theorem namedIndex_none_iff (name : String) (names : List String) (offset : Nat) :
    namedIndex name names offset = none ↔ name ∉ names := by
  simp [namedIndex_eq_idxOf]

theorem symbolIndex_eq_namedIndex (name : String) (symbols : List Symbol) (offset : Nat) :
    symbolIndex name symbols offset = namedIndex name (symbols.map Symbol.name) offset := by
  induction symbols generalizing offset with
  | nil => rfl
  | cons candidate rest ih =>
    simp only [symbolIndex, List.map_cons, namedIndex]
    split
    · rfl
    · exact ih (offset + 1)

theorem symbolIndex_some_iff (name : String) (symbols : List Symbol) (offset id : Nat) :
    symbolIndex name symbols offset = some id ↔
      ∃ relative, FirstNameAt (symbols.map Symbol.name) name relative ∧ offset + relative = id := by
  rw [symbolIndex_eq_namedIndex]
  exact namedIndex_some_iff name (symbols.map Symbol.name) offset id

theorem symbolIndex_none_iff (name : String) (symbols : List Symbol) (offset : Nat) :
    symbolIndex name symbols offset = none ↔ ∀ symbol ∈ symbols, symbol.name ≠ name := by
  rw [symbolIndex_eq_namedIndex, namedIndex_none_iff]
  simp only [List.mem_map, not_exists, not_and]

theorem namedIndex_append (name : String) (before after : List String) (offset : Nat) :
    namedIndex name (before ++ after) offset =
      match namedIndex name before offset with
      | some index => some index
      | none => namedIndex name after (offset + before.length) := by
  induction before generalizing offset with
  | nil => simp [namedIndex]
  | cons candidate rest ih =>
    simp only [List.cons_append, namedIndex, List.length_cons]
    split
    · rfl
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (offset + 1)

theorem namedIndex_first_iff (name : String) (names : List String) (id : Nat) :
    namedIndex name names 0 = some id ↔ FirstNameAt names name id := by
  simp [namedIndex_some_iff]

def NameAllocation (before : List String) (name : String) (id : Nat)
    (after : List String) : Prop :=
  FirstNameAt after name id ∧
  (∃ extra, after = before ++ extra) ∧
  (∀ other oldId, namedIndex other before 0 = some oldId →
    namedIndex other after 0 = some oldId) ∧
  (before.Nodup → after.Nodup)

theorem nameAllocation_existing (names : List String) (name : String) (id : Nat)
    (found : namedIndex name names 0 = some id) : NameAllocation names name id names := by
  exact ⟨(namedIndex_first_iff name names id).mp found, ⟨[], by simp⟩,
    fun _ _ previous => previous, fun unique => unique⟩

theorem nameAllocation_fresh (names : List String) (name : String)
    (missing : namedIndex name names 0 = none) :
    NameAllocation names name names.length (names ++ [name]) := by
  have absent := (namedIndex_none_iff name names 0).mp missing
  refine ⟨?_, ⟨[name], rfl⟩, ?_, ?_⟩
  · apply (namedIndex_first_iff name (names ++ [name]) names.length).mp
    simp [namedIndex_append, missing, namedIndex]
  · intro other oldId previous
    simp [namedIndex_append, previous]
  · intro unique
    apply List.nodup_append.mpr
    refine ⟨unique, by simp, ?_⟩
    intro value member target targetMember same
    have targetSame : target = name := by simpa using targetMember
    exact absent ((same.trans targetSame) ▸ member)

theorem variableId_run (name : String) (state : State) :
    variableId name state =
      match namedIndex name state.variables 0 with
      | some id => .ok (id, state)
      | none => .ok (state.variables.length,
          { state with variables := state.variables ++ [name] }) := by
  cases found : namedIndex name state.variables 0 <;>
    simp [variableId, bind, pure, get, getThe, MonadStateOf.get, set,
      StateT.bind, StateT.get, StateT.pure, StateT.set, Except.pure, Except.bind, found]

theorem reserveSymbol_run (predicate : Bool) (name : String) (state : State) :
    reserveSymbol predicate name state =
      let symbols := if predicate then state.predicates else state.functions
      match symbolIndex name symbols 0 with
      | some id => .ok (id, state)
      | none =>
        let updated := symbols ++ [{ name, arity := none }]
        .ok (symbols.length, if predicate then { state with predicates := updated }
          else { state with functions := updated }) := by
  cases predicate <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;>
    split <;>
    simp_all [reserveSymbol, bind, pure, get, getThe, MonadStateOf.get, set,
      StateT.bind, StateT.get, StateT.pure, StateT.set, Except.pure, Except.bind]

theorem variableId_spec (name : String) (state : State) :
    ∃ id updated, variableId name state = .ok (id, updated) ∧
      NameAllocation state.variables name id updated.variables ∧
      updated.tokens = state.tokens ∧ updated.endOffset = state.endOffset ∧
      updated.functions = state.functions ∧ updated.predicates = state.predicates ∧
      updated.clauseNames = state.clauseNames := by
  rw [variableId_run]
  cases found : namedIndex name state.variables 0 with
  | some id => exact ⟨id, state, rfl, nameAllocation_existing _ _ _ found,
      rfl, rfl, rfl, rfl, rfl⟩
  | none => exact ⟨state.variables.length,
      { state with variables := state.variables ++ [name] }, rfl,
      nameAllocation_fresh _ _ found, rfl, rfl, rfl, rfl, rfl⟩

def selectedSymbolNames (state : State) (predicate : Bool) : List String :=
  (if predicate then state.predicates else state.functions).map Symbol.name

theorem symbolAllocation_existing (symbols : List Symbol) (name : String) (id : Nat)
    (found : symbolIndex name symbols 0 = some id) :
    NameAllocation (symbols.map Symbol.name) name id (symbols.map Symbol.name) := by
  exact nameAllocation_existing _ _ _ ((symbolIndex_eq_namedIndex name symbols 0) ▸ found)

theorem symbolAllocation_fresh (symbols : List Symbol) (name : String)
    (missing : symbolIndex name symbols 0 = none) :
    NameAllocation (symbols.map Symbol.name) name symbols.length
      ((symbols ++ [({ name, arity := none } : Symbol)]).map Symbol.name) := by
  have missingName : namedIndex name (symbols.map Symbol.name) 0 = none := by
    simpa only [symbolIndex_eq_namedIndex] using missing
  simpa only [List.map_append, List.map_cons, List.map_nil, List.length_map] using
    nameAllocation_fresh (symbols.map Symbol.name) name missingName

theorem reserveSymbol_spec (predicate : Bool) (name : String) (state : State) :
    ∃ id updated, reserveSymbol predicate name state = .ok (id, updated) ∧
      NameAllocation (selectedSymbolNames state predicate) name id
        (selectedSymbolNames updated predicate) ∧
      updated.tokens = state.tokens ∧ updated.endOffset = state.endOffset ∧
      updated.variables = state.variables ∧ updated.clauseNames = state.clauseNames ∧
      (if predicate then updated.functions = state.functions
        else updated.predicates = state.predicates) := by
  cases predicate with
  | false =>
    cases found : symbolIndex name state.functions 0 with
    | some id =>
      refine ⟨id, state, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
      · simp [reserveSymbol_run, found]
      · simpa [selectedSymbolNames] using symbolAllocation_existing state.functions name id found
    | none =>
      refine ⟨state.functions.length,
        { state with functions := state.functions ++ [{ name, arity := none }] },
        ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
      · simp [reserveSymbol_run, found]
      · simpa [selectedSymbolNames] using symbolAllocation_fresh state.functions name found
  | true =>
    cases found : symbolIndex name state.predicates 0 with
    | some id =>
      refine ⟨id, state, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
      · simp [reserveSymbol_run, found]
      · simpa [selectedSymbolNames] using symbolAllocation_existing state.predicates name id found
    | none =>
      refine ⟨state.predicates.length,
        { state with predicates := state.predicates ++ [{ name, arity := none }] },
        ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
      · simp [reserveSymbol_run, found]
      · simpa [selectedSymbolNames] using symbolAllocation_fresh state.predicates name found

def NamesUnique (state : State) : Prop :=
  state.variables.Nodup ∧ (state.functions.map Symbol.name).Nodup ∧
    (state.predicates.map Symbol.name).Nodup

theorem variableId_preserves_unique (name : String) (state updated : State) (id : Nat)
    (returned : variableId name state = .ok (id, updated)) (unique : NamesUnique state) :
    NamesUnique updated := by
  obtain ⟨actualId, actualState, actualReturned, allocation, _, _, functions, predicates, _⟩ :=
    variableId_spec name state
  rw [returned] at actualReturned
  cases actualReturned
  exact ⟨allocation.2.2.2 unique.1, functions ▸ unique.2.1, predicates ▸ unique.2.2⟩

theorem reserveSymbol_preserves_unique (predicate : Bool) (name : String)
    (state updated : State) (id : Nat)
    (returned : reserveSymbol predicate name state = .ok (id, updated))
    (unique : NamesUnique state) : NamesUnique updated := by
  obtain ⟨actualId, actualState, actualReturned, allocation, _, _, variables, _, other⟩ :=
    reserveSymbol_spec predicate name state
  rw [returned] at actualReturned
  cases actualReturned
  cases predicate with
  | false =>
    refine ⟨variables ▸ unique.1, ?_, other ▸ unique.2.2⟩
    exact allocation.2.2.2 unique.2.1
  | true =>
    refine ⟨variables ▸ unique.1, other ▸ unique.2.1, ?_⟩
    exact allocation.2.2.2 unique.2.2

end Fang.Frontend

#print axioms Fang.Frontend.namedIndex_some_iff
#print axioms Fang.Frontend.namedIndex_none_iff
#print axioms Fang.Frontend.symbolIndex_some_iff
#print axioms Fang.Frontend.symbolIndex_none_iff
#print axioms Fang.Frontend.variableId_spec
#print axioms Fang.Frontend.reserveSymbol_spec
#print axioms Fang.Frontend.variableId_preserves_unique
#print axioms Fang.Frontend.reserveSymbol_preserves_unique
