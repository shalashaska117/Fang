/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft declaration composition; variables are local, symbols are shared. -/
import QuantifiedTableEncoding
import Fang.FrontendDisjunctionGrammar

namespace Fang.QuantifiedFrontend
open Frontend

inductive TableDeclarationEncoding (state : State) :
    NamedQuantified.Declaration → NamedQuantified.NumericDeclaration → Prop where
  | cnf (variables : List String) (name : String) {named encoded}
      (relation : TableClauseEncoding { state with variables } named encoded) :
      TableDeclarationEncoding state (.cnf ⟨name, named⟩) (.cnf encoded)
  | fof (variables : List String) (name : String) {named encoded}
      (closed : named.Within [])
      (relation : TableFormulaEncoding { state with variables } named encoded) :
      TableDeclarationEncoding state (.fof name named) (.fof encoded)

theorem TableDeclarationEncoding.toSource {state named encoded}
    (encoding : TableDeclarationEncoding state named encoded) :
    NamedQuantified.DeclarationEncoding (signatureFrom state) (symbolsFrom state) named encoded := by
  cases encoding with
  | cnf variables name relation => exact .cnf (variablesFrom variables) (relation.toSource name)
  | fof variables name closed relation => exact .fof name (variablesFrom variables) closed relation.toSource

theorem TableDeclarationEncoding.extend {before after named encoded}
    (encoding : TableDeclarationEncoding before named encoded) (extension : SymbolExtension before after) :
    TableDeclarationEncoding after named encoded := by
  cases encoding with
  | cnf variables name relation =>
    exact .cnf variables name (relation.extend (extension.withVariables variables))
  | fof variables name closed relation =>
    exact .fof variables name closed (relation.extend (extension.withVariables variables))

theorem tableDeclarations_extend {before after named encoded}
    (encoding : Source.RelatedLists (TableDeclarationEncoding before) named encoded)
    (extension : SymbolExtension before after) :
    Source.RelatedLists (TableDeclarationEncoding after) named encoded := by
  induction encoding with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extend extension) ih

theorem tableDeclarations_toSource {state named encoded}
    (encoding : Source.RelatedLists (TableDeclarationEncoding state) named encoded)
    (names : (named.map NamedQuantified.Declaration.name).Nodup) :
    NamedQuantified.ProblemEncoding (signatureFrom state) (symbolsFrom state) named encoded := by
  refine ⟨names, ?_⟩
  clear names
  induction encoding with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.toSource ih

theorem tableDeclarations_unsat {state named encoded}
    (encoding : Source.RelatedLists (TableDeclarationEncoding state) named encoded)
    (names : (named.map NamedQuantified.Declaration.name).Nodup)
    (refuted : ¬ NamedQuantified.NumericSatisfiable encoded) : ¬ NamedQuantified.Satisfiable named :=
  (tableDeclarations_toSource encoding names).unsat refuted

end Fang.QuantifiedFrontend
