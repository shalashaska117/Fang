/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Interpret actual parser tables as the independent named-to-numeric encoding.
These projections are proof definitions, not a second production parser.
-/
import Fang.FrontendArity
import Fang.SourceSemantics

namespace Fang.Frontend

def variablesFrom (names : List String) : Source.Variables where
  id name := (namedIndex name names 0).getD 0
  name id := names[id]?.getD ""

def tableId (symbols : List Symbol) (name : String) : Nat :=
  (symbolIndex name symbols 0).getD 0

def tableName (symbols : List Symbol) (id : Nat) : String :=
  ((symbols[id]?).map Symbol.name).getD ""

def tableArity (symbols : List Symbol) (name : String) : Option Nat := do
  let id ← symbolIndex name symbols 0
  let symbol ← symbols[id]?
  symbol.arity

def symbolsFrom (state : State) : Source.Symbols where
  functionId := tableId state.functions
  functionName := tableName state.functions
  predicateId := tableId state.predicates
  predicateName := tableName state.predicates

def signatureFrom (state : State) : Source.Signature where
  functionArity := tableArity state.functions
  predicateArity := tableArity state.predicates

theorem FirstNameAt.getElem? {names : List String} {name : String} {id : Nat}
    (first : FirstNameAt names name id) : names[id]? = some name := by
  obtain ⟨within, same, _⟩ := first
  simp [List.getElem?_eq_getElem within, same]

theorem variablesFrom_found {names : List String} {name : String} {id : Nat}
    (found : namedIndex name names 0 = some id) :
    (variablesFrom names).id name = id ∧ (variablesFrom names).name id = name := by
  have entry := (namedIndex_first_iff name names id).mp found |>.getElem?
  simp [variablesFrom, found, entry]

theorem variable_encoding_of_found (signature : Source.Signature) (symbols : Source.Symbols)
    {names : List String} {name : String} {id : Nat}
    (found : namedIndex name names 0 = some id) :
    Source.TermEncoding signature symbols (variablesFrom names) (.var name) (.var id) := by
  obtain ⟨assigned, recovered⟩ := variablesFrom_found found
  have roundtrip : (variablesFrom names).name ((variablesFrom names).id name) = name := by
    rw [assigned, recovered]
  simpa only [assigned] using Source.TermEncoding.var (signature := signature)
    (symbols := symbols) (variables := variablesFrom names) name roundtrip

theorem variableId_encoding (name : String) (state updated : State) (id : Nat)
    (returned : variableId name state = .ok (id, updated))
    (signature : Source.Signature) (symbols : Source.Symbols) :
    Source.TermEncoding signature symbols (variablesFrom updated.variables) (.var name) (.var id) := by
  obtain ⟨actualId, actualState, actualReturned, allocation, _⟩ := variableId_spec name state
  rw [returned] at actualReturned
  cases actualReturned
  apply variable_encoding_of_found
  exact (namedIndex_first_iff name updated.variables id).mpr allocation.1

theorem table_found {symbols : List Symbol} {name : String} {id : Nat}
    (found : symbolIndex name symbols 0 = some id) :
    tableId symbols name = id ∧ tableName symbols id = name := by
  have first : FirstNameAt (symbols.map Symbol.name) name id := by
    apply (namedIndex_first_iff name (symbols.map Symbol.name) id).mp
    simpa only [symbolIndex_eq_namedIndex] using found
  have entry := first.getElem?
  simp only [List.getElem?_map] at entry
  simp [tableId, tableName, found, entry]

theorem table_arity_of_found {symbols : List Symbol} {name : String} {id arity : Nat}
    (found : symbolIndex name symbols 0 = some id)
    (checked : (symbols[id]?).map Symbol.arity = some (some arity)) :
    tableArity symbols name = some arity := by
  cases entry : symbols[id]? with
  | none => simp [entry] at checked
  | some symbol =>
      simp only [entry, Option.map_some, Option.some.injEq] at checked
      simp [tableArity, found, entry, checked]

theorem function_encoding_of_found (state : State) (variables : Source.Variables)
    {name : String} {id : Nat} {arguments : List Source.Term} {encoded : List Fang.Term}
    (found : symbolIndex name state.functions 0 = some id)
    (checked : (state.functions[id]?).map Symbol.arity = some (some arguments.length))
    (children : Source.TermsEncoding (signatureFrom state) (symbolsFrom state) variables arguments encoded) :
    Source.TermEncoding (signatureFrom state) (symbolsFrom state) variables
      (.app name arguments) (.app id encoded) := by
  obtain ⟨assigned, recovered⟩ := table_found found
  have roundtrip : (symbolsFrom state).functionName ((symbolsFrom state).functionId name) = name := by
    change tableName state.functions (tableId state.functions name) = name
    rw [assigned, recovered]
  have arity := table_arity_of_found found checked
  simpa only [symbolsFrom, assigned] using Source.TermEncoding.app name arguments encoded roundtrip arity children

theorem literal_encoding_of_found (state : State) (variables : Source.Variables) (positive : Bool)
    {name : String} {id : Nat} {arguments : List Source.Term} {encoded : List Fang.Term}
    (found : symbolIndex name state.predicates 0 = some id)
    (checked : (state.predicates[id]?).map Symbol.arity = some (some arguments.length))
    (children : Source.TermsEncoding (signatureFrom state) (symbolsFrom state) variables arguments encoded) :
    Source.LiteralEncoding (signatureFrom state) (symbolsFrom state) variables
      ⟨positive, name, arguments⟩ ⟨positive, ⟨id, encoded⟩⟩ := by
  obtain ⟨assigned, recovered⟩ := table_found found
  refine ⟨rfl, assigned.symm, ?_, table_arity_of_found found checked, children⟩
  change tableName state.predicates (tableId state.predicates name) = name
  rw [assigned, recovered]

#print axioms variableId_encoding
#print axioms function_encoding_of_found
#print axioms literal_encoding_of_found

end Fang.Frontend
