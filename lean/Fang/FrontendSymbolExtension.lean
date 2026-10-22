/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Transport encodings across clauses while preserving each clause's own variable
assignment. Only function/predicate IDs and known arities cross the reset.
-/
import Fang.FrontendTableEncoding

namespace Fang.Frontend

structure SymbolExtension (before after : State) : Prop where
  symbols : ∀ predicate name id,
    symbolIndex name (symbolTable before predicate) 0 = some id →
    symbolIndex name (symbolTable after predicate) 0 = some id
  arities : ∀ (predicate : Bool) (id arity : Nat),
    ((symbolTable before predicate)[id]?).map Symbol.arity = some (some arity) →
    ((symbolTable after predicate)[id]?).map Symbol.arity = some (some arity)

theorem SymbolExtension.refl (state : State) : SymbolExtension state state :=
  ⟨fun _ _ _ found => found, fun _ _ _ found => found⟩

theorem SymbolExtension.trans {first second third : State}
    (left : SymbolExtension first second) (right : SymbolExtension second third) :
    SymbolExtension first third :=
  ⟨fun predicate name id found => right.symbols predicate name id
      (left.symbols predicate name id found),
   fun predicate id arity found => right.arities predicate id arity
      (left.arities predicate id arity found)⟩

theorem TableExtension.toSymbolExtension {before after : State}
    (extension : TableExtension before after) : SymbolExtension before after :=
  ⟨extension.symbols, extension.arities⟩

theorem symbolExtension_of_same_tables {before after : State}
    (functions : after.functions = before.functions)
    (predicates : after.predicates = before.predicates) : SymbolExtension before after := by
  constructor
  · intro predicate name id found
    simpa only [symbolTable, functions, predicates] using found
  · intro predicate id arity found
    simpa only [symbolTable, functions, predicates] using found

theorem symbolExtension_reset (state : State) (variables clauseNames : List String) :
    SymbolExtension state { state with variables, clauseNames } :=
  symbolExtension_of_same_tables rfl rfl

theorem SymbolExtension.withVariables {before after : State}
    (extension : SymbolExtension before after) (variables : List String) :
    TableExtension { before with variables } { after with variables } := by
  constructor
  · intro name id found; exact found
  · exact extension.symbols
  · exact extension.arities

theorem tableArity_some {symbols : List Symbol} {name : String} {arity : Nat}
    (known : tableArity symbols name = some arity) :
    ∃ id, symbolIndex name symbols 0 = some id ∧
      (symbols[id]?).map Symbol.arity = some (some arity) := by
  cases found : symbolIndex name symbols 0 with
  | none => simp [tableArity, found] at known
  | some id =>
      cases entry : symbols[id]? with
      | none => simp [tableArity, found, entry] at known
      | some symbol =>
          simp only [tableArity, found, entry, bind, Option.bind] at known
          exact ⟨id, rfl, by simp [entry, known]⟩

theorem SymbolExtension.table_arity {before after : State}
    (extension : SymbolExtension before after) (predicate : Bool) (name : String) (arity : Nat)
    (known : tableArity (symbolTable before predicate) name = some arity) :
    tableArity (symbolTable after predicate) name = some arity ∧
      tableId (symbolTable after predicate) name = tableId (symbolTable before predicate) name ∧
      tableName (symbolTable after predicate) (tableId (symbolTable after predicate) name) = name := by
  obtain ⟨id, found, checked⟩ := tableArity_some known
  have newFound := extension.symbols predicate name id found
  have newChecked := extension.arities predicate id arity checked
  obtain ⟨oldId, _⟩ := table_found found
  obtain ⟨newId, newName⟩ := table_found newFound
  exact ⟨table_arity_of_found newFound newChecked, newId.trans oldId.symm,
    by rw [newId, newName]⟩

theorem TableTermEncoding.freeze_variables {before after named encoded}
    (encoding : TableTermEncoding before named encoded) (extension : SymbolExtension before after) :
    TableTermEncoding { after with variables := before.variables } named encoded :=
  encoding.extend (extension.withVariables before.variables)

theorem TableTermsEncoding.freeze_variables {before after named encoded}
    (encoding : TableTermsEncoding before named encoded) (extension : SymbolExtension before after) :
    TableTermsEncoding { after with variables := before.variables } named encoded :=
  encoding.extend (extension.withVariables before.variables)

theorem TableLiteralEncoding.freeze_variables {before after named encoded}
    (encoding : TableLiteralEncoding before named encoded) (extension : SymbolExtension before after) :
    TableLiteralEncoding { after with variables := before.variables } named encoded :=
  encoding.extend (extension.withVariables before.variables)

end Fang.Frontend

namespace Fang.Source

open Frontend

mutual
theorem TermEncoding.extend_symbols {before after : State} {variables named encoded}
    (encoding : TermEncoding (signatureFrom before) (symbolsFrom before) variables named encoded)
    (extension : SymbolExtension before after) :
    TermEncoding (signatureFrom after) (symbolsFrom after) variables named encoded := by
  cases encoding with
  | var name roundtrip => exact .var name roundtrip
  | app name arguments encoded roundtrip arity children =>
      obtain ⟨newArity, sameId, newRoundtrip⟩ := extension.table_arity false name arguments.length arity
      simp only [symbolTable, Bool.false_eq_true, ↓reduceIte] at sameId
      simpa only [symbolsFrom, sameId] using
        TermEncoding.app (signature := signatureFrom after) (symbols := symbolsFrom after)
          (variables := variables) name arguments encoded newRoundtrip newArity
          (children.extend_symbols extension)

theorem TermsEncoding.extend_symbols {before after : State} {variables named encoded}
    (encoding : TermsEncoding (signatureFrom before) (symbolsFrom before) variables named encoded)
    (extension : SymbolExtension before after) :
    TermsEncoding (signatureFrom after) (symbolsFrom after) variables named encoded := by
  cases encoding with
  | nil => exact .nil
  | cons head tail => exact .cons (head.extend_symbols extension) (tail.extend_symbols extension)
end

theorem LiteralEncoding.extend_symbols {before after : State} {variables named encoded}
    (encoding : LiteralEncoding (signatureFrom before) (symbolsFrom before) variables named encoded)
    (extension : SymbolExtension before after) :
    LiteralEncoding (signatureFrom after) (symbolsFrom after) variables named encoded := by
  obtain ⟨newArity, sameId, newRoundtrip⟩ := extension.table_arity true named.predicate
    named.arguments.length encoding.arity
  refine ⟨encoding.polarity, ?_, newRoundtrip, newArity, encoding.arguments.extend_symbols extension⟩
  exact encoding.predicate.trans sameId.symm

theorem RelatedLists.imp {α β : Type} {first second : α → β → Prop} {inputs outputs}
    (related : RelatedLists first inputs outputs)
    (transfer : ∀ input output, first input output → second input output) :
    RelatedLists second inputs outputs := by
  induction related with
  | nil => exact .nil
  | cons head tail induction => exact .cons (transfer _ _ head) induction

theorem ClauseEncoding.extend_symbols {before after : State} {variables named encoded}
    (encoding : ClauseEncoding (signatureFrom before) (symbolsFrom before) variables named encoded)
    (extension : SymbolExtension before after) :
    ClauseEncoding (signatureFrom after) (symbolsFrom after) variables named encoded :=
  encoding.imp (fun _ _ proof => proof.extend_symbols extension)

theorem ProblemEncoding.extend_symbols {before after : State} {named encoded}
    (encoding : ProblemEncoding (signatureFrom before) (symbolsFrom before) named encoded)
    (extension : SymbolExtension before after) :
    ProblemEncoding (signatureFrom after) (symbolsFrom after) named encoded := by
  refine ⟨encoding.uniqueNames, encoding.clauses.imp ?_⟩
  rintro named encoded ⟨variables, headEncoding⟩
  exact ⟨variables, headEncoding.extend_symbols extension⟩

end Fang.Source

#print axioms Fang.Frontend.symbolExtension_reset
#print axioms Fang.Frontend.SymbolExtension.withVariables
#print axioms Fang.Frontend.TableTermEncoding.freeze_variables
#print axioms Fang.Source.TermEncoding.extend_symbols
#print axioms Fang.Source.LiteralEncoding.extend_symbols
#print axioms Fang.Source.ClauseEncoding.extend_symbols
#print axioms Fang.Source.ProblemEncoding.extend_symbols
