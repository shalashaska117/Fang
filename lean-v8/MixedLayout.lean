/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Source-ordered mixed assembly, independently specified from the Rust wrapper. -/
import QuantifiedProblem
import Fang.Checker

namespace Fang.QuantifiedCertificate
open NamedQuantified

def retained : List NumericDeclaration → Problem
  | [] => []
  | .cnf clause :: rest => clause :: retained rest
  | .fof _ :: rest => retained rest

def formulas : List NumericDeclaration → List QuantifiedFOF.Formula
  | [] => []
  | .cnf _ :: rest => formulas rest
  | .fof formula :: rest => formula :: formulas rest

/-- Each FOF declaration consumes exactly one ordered raw clause block. CNF
    declarations keep their position. Only duplicate literals are removed. -/
inductive MixedLayout : List NumericDeclaration → List Problem → Problem → Prop where
  | nil : MixedLayout [] [] []
  | cnf {source blocks prepared} (clause : Clause)
      (tail : MixedLayout source blocks prepared) :
      MixedLayout (.cnf clause :: source) blocks (dedup clause :: prepared)
  | fof {source blocks prepared} (formula : QuantifiedFOF.Formula) (block : Problem)
      (tail : MixedLayout source blocks prepared) :
      MixedLayout (.fof formula :: source) (block :: blocks) (preprocess block ++ prepared)

theorem mixedLayout_block_count {source blocks prepared} (layout : MixedLayout source blocks prepared) :
    blocks.length = (formulas source).length := by
  induction layout with
  | nil => rfl
  | cnf _ _ ih => exact ih
  | fof _ _ _ ih => simp only [formulas, List.length_cons, ih]

theorem mixedLayout_clause_count {source blocks prepared} (layout : MixedLayout source blocks prepared) :
    prepared.length = (retained source).length + (blocks.map List.length).sum := by
  induction layout with
  | nil => rfl
  | cnf _ _ ih => simp only [retained, List.length_cons, ih]; omega
  | fof _ _ _ ih =>
    simp only [retained, preprocess, List.length_append, List.length_map, List.map_cons, List.sum_cons, ih]
    omega

theorem models_cons {D : Type} (model : Interpretation D) (clause : Clause) (problem : Problem) :
    Problem.Models model (clause :: problem) ↔ clause.Valid model ∧ problem.Models model := by
  simp only [Problem.Models, List.forall_mem_cons]

theorem models_append {D : Type} (model : Interpretation D) (left right : Problem) :
    Problem.Models model (left ++ right) ↔ left.Models model ∧ right.Models model := by
  simp only [Problem.Models, List.mem_append, or_imp, forall_and]

/-- The indexed search input and the regrouped semantic problem have the same
    models. This theorem does not yet connect the relation to `prepare`. -/
theorem mixedLayout_models {source blocks prepared} (layout : MixedLayout source blocks prepared)
    {D : Type} (model : Interpretation D) :
    prepared.Models model ↔ (retained source).Models model ∧ Problem.Models model blocks.flatten := by
  induction layout with
  | nil => simp [retained, Problem.Models]
  | cnf clause tail ih =>
    simp only [retained, models_cons, dedup_preserves_models, ih, and_assoc]
  | fof formula block tail ih =>
    simp only [retained, List.flatten_cons, models_append, preprocess_preserves_models, ih]
    exact and_left_comm

theorem mixedLayout_regrouped {source blocks prepared} (layout : MixedLayout source blocks prepared)
    {D : Type} (model : Interpretation D) :
    prepared.Models model ↔ (retained source ++ blocks.flatten).Models model := by
  rw [models_append]
  exact mixedLayout_models layout model

theorem mixedLayout_check_unsat {source blocks prepared} (layout : MixedLayout source blocks prepared)
    (certificate : Certificate) (accepted : check prepared certificate = true) :
    ¬ Satisfiable (retained source ++ blocks.flatten) := by
  rintro ⟨D, inhabited, model, holds⟩
  exact check_sound prepared certificate accepted
    ⟨D, inhabited, model, (mixedLayout_regrouped layout model).mpr holds⟩

end Fang.QuantifiedCertificate
