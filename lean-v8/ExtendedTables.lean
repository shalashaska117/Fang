/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Check the tables supplied by the Rust pipeline before exporting formulas.
   Rust retains responsibility for choosing fresh names. -/
import NamedBinding

namespace Fang.QuantifiedTstp.Tables
open Frontend QuantifiedFrontend

def sameSymbol (left right : Symbol) : Bool :=
  left.name == right.name && left.arity == right.arity

def isPrefix : List Symbol → List Symbol → Bool
  | [], _ => true
  | _ :: _, [] => false
  | old :: olds, new :: news => sameSymbol old new && isPrefix olds news

theorem sameSymbol_eq {left right} (checked : sameSymbol left right = true) : left = right := by
  cases left with
  | mk name arity =>
    cases right with
    | mk otherName otherArity =>
      simp only [sameSymbol, Bool.and_eq_true, beq_iff_eq] at checked
      cases checked.1
      cases checked.2
      rfl

theorem prefix_append {before after} (checked : isPrefix before after = true) :
    ∃ extra, after = before ++ extra := by
  induction before generalizing after with
  | nil => exact ⟨after, rfl⟩
  | cons first rest ih =>
    cases after with
    | nil => simp [isPrefix] at checked
    | cons next tail =>
      simp only [isPrefix, Bool.and_eq_true] at checked
      have same := sameSymbol_eq checked.1
      obtain ⟨extra, restSame⟩ := ih checked.2
      exact ⟨extra, by simp [same, restSame]⟩

def validSymbols (symbols : List Symbol) : Bool :=
  decide (symbols.map Symbol.name).Nodup &&
    symbols.all (fun entry => lowerName entry.name && entry.arity.isSome)

def validVariables (names : List String) : Bool :=
  decide names.Nodup && names.all variableName

/-- All original function entries must survive unchanged at their exact IDs.
    Predicates come from the original table and cannot be replaced by a caller.
    Both arity vectors are supplied by the checked preprocessing result. -/
def checkedState (original : State) (functions : List Symbol) (variables : List String)
    (functionArities predicateArities : List Nat) : Except String State := do
  if !isPrefix original.functions functions then
    .error "export-error: original function table changed"
  if functions.map Symbol.arity != functionArities.map some then
    .error "export-error: prepared function arities differ"
  if original.predicates.map Symbol.arity != predicateArities.map some then
    .error "export-error: prepared predicate arities differ"
  if !validSymbols functions || !validSymbols original.predicates then
    .error "export-error: invalid or duplicate symbol name"
  if !validVariables variables then
    .error "export-error: invalid or duplicate variable name"
  pure { original with functions, variables }

theorem append_symbolExtension (original : State) (extra : List Symbol) (variables : List String) :
    SymbolExtension original { original with functions := original.functions ++ extra, variables } := by
  constructor
  · intro predicate name id found
    cases predicate with
    | true => exact found
    | false =>
      change symbolIndex name (original.functions ++ extra) 0 = some id
      change symbolIndex name original.functions 0 = some id at found
      rw [symbolIndex_eq_namedIndex, List.map_append, namedIndex_append,
        ← symbolIndex_eq_namedIndex, found]
  · intro predicate id arity found
    cases predicate with
    | true => exact found
    | false =>
      change ((original.functions ++ extra)[id]?).map Symbol.arity = some (some arity)
      change (original.functions[id]?).map Symbol.arity = some (some arity) at found
      obtain ⟨entry, present, known⟩ := Option.map_eq_some_iff.mp found
      rw [getElem?_append_preserves _ _ _ _ present]
      exact congrArg some known

theorem checkedState_spec {original functions variables functionArities predicateArities state}
    (success : checkedState original functions variables functionArities predicateArities = .ok state) :
    state = { original with functions, variables } ∧
    (∃ extra, functions = original.functions ++ extra) ∧
    functions.map Symbol.arity = functionArities.map some ∧
    original.predicates.map Symbol.arity = predicateArities.map some ∧
    validSymbols functions = true ∧ validSymbols original.predicates = true ∧
    validVariables variables = true := by
  by_cases samePrefix : isPrefix original.functions functions = true
  · by_cases functionsMatch : functions.map Symbol.arity = functionArities.map some
    · by_cases predicatesMatch : original.predicates.map Symbol.arity = predicateArities.map some
      · by_cases validFunctions : validSymbols functions = true
        · by_cases validPredicates : validSymbols original.predicates = true
          · by_cases validVars : validVariables variables = true
            · simp [checkedState, samePrefix, functionsMatch, predicatesMatch,
                validFunctions, validPredicates, validVars, pure, Except.pure] at success
              exact ⟨success.symm, prefix_append samePrefix, functionsMatch, predicatesMatch,
                validFunctions, validPredicates, validVars⟩
            · simp [checkedState, samePrefix, functionsMatch, predicatesMatch,
                validFunctions, validPredicates, validVars, bind, Except.bind] at success
          · simp [checkedState, samePrefix, functionsMatch, predicatesMatch,
              validFunctions, validPredicates, bind, Except.bind] at success
        · simp [checkedState, samePrefix, functionsMatch, predicatesMatch,
            validFunctions, bind, Except.bind] at success
      · simp [checkedState, samePrefix, functionsMatch, predicatesMatch, bind, Except.bind] at success
    · simp [checkedState, samePrefix, functionsMatch, bind, Except.bind] at success
  · simp [checkedState, samePrefix, bind, Except.bind] at success

theorem checkedState_extension {original functions variables functionArities predicateArities state}
    (success : checkedState original functions variables functionArities predicateArities = .ok state) :
    SymbolExtension original state := by
  obtain ⟨same, ⟨extra, appended⟩, _⟩ := checkedState_spec success
  subst state
  rw [appended]
  exact append_symbolExtension original extra variables

/-- Original bodies keep their own binder table when carried into the new
    signature. Prepared formulas may use a different rectified variable table. -/
theorem original_encoding {original functions variables functionArities predicateArities state named numeric}
    (success : checkedState original functions variables functionArities predicateArities = .ok state)
    (encoding : TableFormulaEncoding original named numeric) :
    TableFormulaEncoding { state with variables := original.variables } named numeric :=
  encoding.freeze_variables (checkedState_extension success)

def renderClosed (original : State) (functions : List Symbol) (variables : List String)
    (functionArities predicateArities : List Nat) (value : QuantifiedFOF.Formula) : Except String String := do
  let state ← checkedState original functions variables functionArities predicateArities
  Naming.renderClosed state value

theorem renderClosed_correct {original functions variables functionArities predicateArities value text}
    (success : renderClosed original functions variables functionArities predicateArities value = .ok text) :
    ∃ state named,
      checkedState original functions variables functionArities predicateArities = .ok state ∧
      SymbolExtension original state ∧
      Bytes.ParsesFormula (Source.Grammar.spelling text) named ∧ named.Within [] ∧
      TableFormulaEncoding state named value := by
  cases checked : checkedState original functions variables functionArities predicateArities with
  | error message => simp [renderClosed, checked, bind, Except.bind] at success
  | ok state =>
    have rendered : Naming.renderClosed state value = .ok text := by
      simpa [renderClosed, checked, bind, Except.bind] using success
    obtain ⟨named, parsed, closed, encoded⟩ := Naming.renderClosed_correct rendered
    exact ⟨state, named, rfl, checkedState_extension checked, parsed, closed, encoded⟩

#print axioms Fang.QuantifiedTstp.Tables.sameSymbol_eq
#print axioms Fang.QuantifiedTstp.Tables.prefix_append
#print axioms Fang.QuantifiedTstp.Tables.append_symbolExtension
#print axioms Fang.QuantifiedTstp.Tables.checkedState_spec
#print axioms Fang.QuantifiedTstp.Tables.checkedState_extension
#print axioms Fang.QuantifiedTstp.Tables.original_encoding
#print axioms Fang.QuantifiedTstp.Tables.renderClosed_correct

end Fang.QuantifiedTstp.Tables
