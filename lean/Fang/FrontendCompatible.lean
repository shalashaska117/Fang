/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Existing symbol tables agree with a fixed source signature wherever an arity
is known. Unknown reservations remain allowed during recursive parsing.
-/
import Fang.FrontendTermGrammar
import Fang.SourceWellFormed
import Fang.SourceAsciiValidity

namespace Fang.Frontend

def TableCompatible (arity : String → Option Nat) (symbols : List Symbol) : Prop :=
  ∀ symbol ∈ symbols, ∀ count, symbol.arity = some count → arity symbol.name = some count

def SignatureCompatible (signature : Source.Signature) (state : State) : Prop :=
  TableCompatible signature.functionArity state.functions ∧
  TableCompatible signature.predicateArity state.predicates

def signatureArity (signature : Source.Signature) (predicate : Bool) : String → Option Nat :=
  if predicate then signature.predicateArity else signature.functionArity

theorem SignatureCompatible.table {signature state} (compatible : SignatureCompatible signature state)
    (predicate : Bool) : TableCompatible (signatureArity signature predicate) (symbolTable state predicate) := by
  cases predicate
  · exact compatible.1
  · exact compatible.2

theorem TableCompatible.append_unknown {arity symbols} (compatible : TableCompatible arity symbols)
    (name : String) : TableCompatible arity (symbols ++ [{ name, arity := none }]) := by
  intro symbol member count known
  rcases List.mem_append.mp member with old | fresh
  · exact compatible symbol old count known
  · simp only [List.mem_singleton] at fresh
    subst symbol
    cases known

theorem SignatureCompatible.same_tables {signature before after}
    (compatible : SignatureCompatible signature before)
    (functions : after.functions = before.functions) (predicates : after.predicates = before.predicates) :
    SignatureCompatible signature after := by
  simpa only [SignatureCompatible, functions, predicates] using compatible

theorem SignatureCompatible.tokens {signature state} (compatible : SignatureCompatible signature state)
    (tokens : List Token) : SignatureCompatible signature { state with tokens } := compatible

theorem variableId_compatible {signature name state id updated}
    (compatible : SignatureCompatible signature state)
    (returned : variableId name state = .ok (id, updated)) : SignatureCompatible signature updated := by
  obtain ⟨actual, final, success, _, _, _, functions, predicates, _⟩ := variableId_spec name state
  rw [returned] at success
  cases success
  exact compatible.same_tables functions predicates

theorem reserveSymbol_compatible {signature predicate name state id updated}
    (compatible : SignatureCompatible signature state)
    (returned : reserveSymbol predicate name state = .ok (id, updated)) :
    SignatureCompatible signature updated := by
  rw [reserveSymbol_run] at returned
  cases predicate <;> simp only [Bool.false_eq_true, ↓reduceIte] at returned
  · cases existing : symbolIndex name state.functions 0 with
    | some previous => simp only [existing] at returned; cases returned; exact compatible
    | none =>
      simp only [existing] at returned
      cases returned
      exact ⟨compatible.1.append_unknown name, compatible.2⟩
  · cases existing : symbolIndex name state.predicates 0 with
    | some previous => simp only [existing] at returned; cases returned; exact compatible
    | none =>
      simp only [existing] at returned
      cases returned
      exact ⟨compatible.1, compatible.2.append_unknown name⟩

theorem TableCompatible.set {arity symbols} (compatible : TableCompatible arity symbols)
    (id : Nat) (entry : Symbol) (count : Nat) (declared : arity entry.name = some count) :
    TableCompatible arity (symbols.set id { entry with arity := some count }) := by
  induction symbols generalizing id with
  | nil => simp [TableCompatible]
  | cons head tail induction =>
    cases id with
    | zero =>
      intro symbol member knownCount known
      rcases List.mem_cons.mp member with rfl | member
      · cases known
        exact declared
      · exact compatible symbol (List.mem_cons_of_mem head member) knownCount known
    | succ id =>
      intro symbol member knownCount known
      rcases List.mem_cons.mp member with rfl | member
      · exact compatible symbol List.mem_cons_self knownCount known
      · exact induction (fun item present => compatible item (List.mem_cons_of_mem head present))
          id symbol member knownCount known

theorem SignatureCompatible.replace {signature state predicate symbols}
    (compatible : SignatureCompatible signature state)
    (selected : TableCompatible (signatureArity signature predicate) symbols) :
    SignatureCompatible signature (replaceSymbolTable state predicate symbols) := by
  cases predicate
  · exact ⟨selected, compatible.2⟩
  · exact ⟨compatible.1, selected⟩

theorem symbolIndex_entry {symbols : List Symbol} {name : String} {id : Nat}
    (found : symbolIndex name symbols 0 = some id) :
    ∃ entry, symbols[id]? = some entry ∧ entry.name = name := by
  have first : FirstNameAt (symbols.map Symbol.name) name id := by
    apply (namedIndex_first_iff name _ id).mp
    simpa only [symbolIndex_eq_namedIndex] using found
  have entry := first.getElem?
  rw [List.getElem?_map] at entry
  exact Option.map_eq_some_iff.mp entry

theorem checkArity_complete {signature state predicate name id count offset}
    (compatible : SignatureCompatible signature state)
    (found : symbolIndex name (symbolTable state predicate) 0 = some id)
    (declared : signatureArity signature predicate name = some count) :
    ∃ updated, checkArity predicate id count offset state = .ok ((), updated) ∧
      SignatureCompatible signature updated := by
  obtain ⟨entry, present, named⟩ := symbolIndex_entry found
  have member := List.mem_of_getElem? present
  cases known : entry.arity with
  | none =>
    refine ⟨_, checkArity_initializes predicate id count offset state entry present known, ?_⟩
    exact compatible.replace ((compatible.table predicate).set id entry count (named ▸ declared))
  | some oldCount =>
    have old := compatible.table predicate entry member oldCount known
    rw [named, declared] at old
    cases old
    exact ⟨state, checkArity_accepts_consistent predicate id count offset state entry present known, compatible⟩

theorem RawTokenSpelling.lower_valid {raw : Token} {name : String}
    (classified : RawTokenSpelling raw (.lower name)) :
    raw.text = name ∧ lowerName raw.text = true ∧ variableName raw.text = false := by
  have text := classified.text
  change raw.text = name at text
  have valid : Source.Grammar.LowerName name := by
    rcases classified with word | ⟨byte, punctuation, _⟩
    · cases word with | lower _ _ valid => exact valid
    · cases punctuation
  have bytes := Source.Grammar.WordSpelling.ascii (.lower name rfl valid)
  have lower := (lowerName_iff name (Source.Grammar.string_ascii_of_spelling name bytes)).mpr valid
  refine ⟨text, text ▸ lower, ?_⟩
  cases variableResult : variableName raw.text with
  | false => rfl
  | true =>
    have impossible := classified.is_variable variableResult
    cases impossible

theorem RawTokenSpelling.variable_valid {raw : Token} {name : String}
    (classified : RawTokenSpelling raw (.variable name)) :
    raw.text = name ∧ variableName raw.text = true := by
  have text := classified.text
  change raw.text = name at text
  have valid : Source.Grammar.VariableName name := by
    rcases classified with word | ⟨byte, punctuation, _⟩
    · cases word with | variableWord _ _ valid => exact valid
    · cases punctuation
  have bytes := Source.Grammar.WordSpelling.ascii (.variableWord name rfl valid)
  exact ⟨text, text ▸ (variableName_iff name (Source.Grammar.string_ascii_of_spelling name bytes)).mpr valid⟩

end Fang.Frontend

#print axioms Fang.Frontend.reserveSymbol_compatible
#print axioms Fang.Frontend.checkArity_complete
#print axioms Fang.Frontend.RawTokenSpelling.lower_valid
#print axioms Fang.Frontend.RawTokenSpelling.variable_valid
