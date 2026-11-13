/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Mixed CNF/closed-FOF axiom semantics. Conjecture roles are not defined here. -/
import QuantifiedEncoding

namespace Fang.NamedQuantified

inductive Declaration where
  | cnf : Source.Clause → Declaration
  | fof : String → Formula → Declaration

inductive NumericDeclaration where
  | cnf : Fang.Clause → NumericDeclaration
  | fof : QuantifiedFOF.Formula → NumericDeclaration

def Declaration.name : Declaration → String
  | .cnf clause => clause.name
  | .fof name _ => name

/-- FOF closure is required explicitly; it is not an implicit quantification rule. -/
def Declaration.Models {D : Type} (model : Source.Interpretation D) : Declaration → Prop
  | .cnf clause => clause.Valid model
  | .fof _ formula => formula.Within [] ∧ ∀ valuation, formula.Holds model valuation

def NumericDeclaration.Models {D : Type} (model : Fang.Interpretation D) : NumericDeclaration → Prop
  | .cnf clause => clause.Valid model
  | .fof formula => formula.Within [] ∧ ∀ valuation, formula.Holds model valuation

inductive DeclarationEncoding (signature : Source.Signature) (symbols : Source.Symbols) :
    Declaration → NumericDeclaration → Prop where
  | cnf {source target} (variables : Source.Variables)
      (relation : Source.ClauseEncoding signature symbols variables source target) :
      DeclarationEncoding signature symbols (.cnf source) (.cnf target)
  | fof (name : String) {source target} (variables : Source.Variables)
      (closed : source.Within []) (relation : Encoding signature symbols variables source target) :
      DeclarationEncoding signature symbols (.fof name source) (.fof target)

theorem DeclarationEncoding.models_toNumeric {signature symbols source target}
    (encoding : DeclarationEncoding signature symbols source target)
    {D : Type} (model : Source.Interpretation D) (holds : source.Models model) :
    target.Models (model.toNumeric symbols) := by
  cases encoding with
  | cnf variables relation => exact relation.valid_toNumeric model holds
  | fof name variables closed relation =>
    refine ⟨by simpa using relation.within [] closed, ?_⟩
    intro valuation
    exact (relation.holds_toNumeric model valuation).mpr (holds.2 _)

theorem DeclarationEncoding.models_toNamed {signature symbols source target}
    (encoding : DeclarationEncoding signature symbols source target)
    {D : Type} (model : Fang.Interpretation D) (holds : target.Models model) :
    source.Models (Source.numericToNamed model symbols) := by
  cases encoding with
  | cnf variables relation => exact relation.valid_toNamed model holds
  | fof name variables closed relation =>
    refine ⟨closed, ?_⟩
    intro valuation
    exact (relation.holds_toNamed model valuation).mpr (holds.2 _)

def Models {D : Type} (model : Source.Interpretation D) (problem : List Declaration) : Prop :=
  ∀ declaration ∈ problem, declaration.Models model

def NumericModels {D : Type} (model : Fang.Interpretation D) (problem : List NumericDeclaration) : Prop :=
  ∀ declaration ∈ problem, declaration.Models model

def Satisfiable (problem : List Declaration) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D), Models model problem

def NumericSatisfiable (problem : List NumericDeclaration) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D), NumericModels model problem

structure ProblemEncoding (signature : Source.Signature) (symbols : Source.Symbols)
    (source : List Declaration) (target : List NumericDeclaration) : Prop where
  uniqueNames : (source.map Declaration.name).Nodup
  declarations : Source.RelatedLists (DeclarationEncoding signature symbols) source target

theorem ProblemEncoding.satisfiable_iff {signature symbols source target}
    (encoding : ProblemEncoding signature symbols source target) :
    Satisfiable source ↔ NumericSatisfiable target := by
  constructor
  · rintro ⟨D, inhabited, model, holds⟩
    refine ⟨D, inhabited, model.toNumeric symbols, ?_⟩
    intro output member
    obtain ⟨input, inputMember, relation⟩ := encoding.declarations.member_right member
    exact relation.models_toNumeric model (holds input inputMember)
  · rintro ⟨D, inhabited, model, holds⟩
    refine ⟨D, inhabited, Source.numericToNamed model symbols, ?_⟩
    intro input member
    obtain ⟨output, outputMember, relation⟩ := encoding.declarations.member_left member
    exact relation.models_toNamed model (holds output outputMember)

/-- Conditional transport only: a numeric refutation/checker must still establish
    the supplied premise, and byte decoding must construct this encoding. -/
theorem ProblemEncoding.unsat {signature symbols source target}
    (encoding : ProblemEncoding signature symbols source target)
    (refuted : ¬ NumericSatisfiable target) : ¬ Satisfiable source :=
  fun model => refuted (encoding.satisfiable_iff.mp model)

end Fang.NamedQuantified
