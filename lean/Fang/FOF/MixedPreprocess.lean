/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see the repository LICENSE.

Independent AST-level composition for mixed CNF and ground-FOF axioms.
Groundness and connection to source bytes are separate parser obligations.
-/
import Fang.FOF.GroundFormula

namespace Fang.GroundFOF

inductive Declaration where
  | cnf : Clause → Declaration
  | fof : Formula → Declaration
  deriving Repr

def Declaration.Models {D : Type} (M : Interpretation D) : Declaration → Prop
  | .cnf c => c.Valid M
  | .fof f => ∀ ρ, f.Holds M ρ

def Declaration.clauses : Declaration → Problem
  | .cnf c => [c]
  | .fof f => f.clausify

def DeclarationsModels {D : Type} (M : Interpretation D)
    (declarations : List Declaration) : Prop :=
  ∀ declaration ∈ declarations, declaration.Models M

/-- Preserve declaration order and each formula's deterministic clause order. -/
def lowerDeclarations (declarations : List Declaration) : Problem :=
  declarations.flatMap Declaration.clauses

/-- The existing stable literal deduplication is applied after concatenation. -/
def prepareDeclarations (declarations : List Declaration) : Problem :=
  Fang.preprocess (lowerDeclarations declarations)

theorem declaration_models {D : Type} (M : Interpretation D) (d : Declaration) :
    d.clauses.Models M ↔ d.Models M := by
  cases d with
  | cnf c => simp [Declaration.clauses, Declaration.Models, Problem.Models]
  | fof f => exact clausify_models M f

theorem lowerDeclarations_models {D : Type} (M : Interpretation D)
    (declarations : List Declaration) :
    (lowerDeclarations declarations).Models M ↔ DeclarationsModels M declarations := by
  constructor
  · intro h d hd
    apply (declaration_models M d).mp
    intro c hc
    exact h c (List.mem_flatMap.mpr ⟨d, hd, hc⟩)
  · intro h c hc
    obtain ⟨d, hd, hcd⟩ := List.mem_flatMap.mp hc
    exact (declaration_models M d).mpr (h d hd) c hcd

theorem prepareDeclarations_models {D : Type} (M : Interpretation D)
    (declarations : List Declaration) :
    (prepareDeclarations declarations).Models M ↔ DeclarationsModels M declarations := by
  exact (preprocess_preserves_models M (lowerDeclarations declarations)).trans
    (lowerDeclarations_models M declarations)

def DeclarationsSatisfiable (declarations : List Declaration) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (M : Interpretation D), DeclarationsModels M declarations

theorem prepareDeclarations_satisfiable (declarations : List Declaration) :
    Satisfiable (prepareDeclarations declarations) ↔ DeclarationsSatisfiable declarations := by
  constructor
  · rintro ⟨D, hD, M, h⟩
    exact ⟨D, hD, M, (prepareDeclarations_models M declarations).mp h⟩
  · rintro ⟨D, hD, M, h⟩
    exact ⟨D, hD, M, (prepareDeclarations_models M declarations).mpr h⟩

/-- This is the needed UNSAT direction at AST level, with no source-byte claim. -/
theorem declarations_unsat_of_prepared_unsat (declarations : List Declaration)
    (h : ¬ Satisfiable (prepareDeclarations declarations)) :
    ¬ DeclarationsSatisfiable declarations := by
  intro hs
  exact h ((prepareDeclarations_satisfiable declarations).mpr hs)

end Fang.GroundFOF
