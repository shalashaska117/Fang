/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Whole-call refinement of the actual generated recursive Skolem transformer. -/
import TransformExistential

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

/-- Termination is in the generated Result model. Structural scope, globally
    distinct rectified binder IDs and scalar stack headroom are caller premises.
    No premise assumes that a Skolemized target already exists. -/
theorem transform_spec (before : Transformer) (formula : Nnf) (limits : Limits)
    (valid : UniversalValid before.universals)
    (ready : TransformReady (universalIds before.universals) formula)
    (room : TransformRoom before formula) :
    Transformer.transform before formula limits ⦃ TransformPost before formula ⦄ := by
  cases formula_eq : formula with
  | Literal literal => exact transform_literal_spec before literal limits valid
  | True => exact transform_constant_spec before true limits valid
  | False => exact transform_constant_spec before false limits valid
  | And left right | Or left right =>
    rw [formula_eq] at ready room
    have children : TransformReady (universalIds before.universals) left ∧
        TransformReady (universalIds before.universals) right := by
      exact transformReady_and ready
    have leftChecked (state : Transformer) (stateValid : UniversalValid state.universals)
        (ids : universalIds state.universals = universalIds before.universals) :
        Transformer.transform state left limits ⦃ TransformPost state left ⦄ := by
      have depth := congrArg List.length ids
      simp only [universalIds_length state.universals stateValid,
        universalIds_length before.universals valid] at depth
      apply transform_spec state left limits stateValid
      · rw [ids]; exact children.1
      · unfold TransformRoom at room ⊢
        simp only [nnfBinders, List.length_append] at room
        omega
    have rightChecked (state : Transformer) (stateValid : UniversalValid state.universals)
        (ids : universalIds state.universals = universalIds before.universals) :
        Transformer.transform state right limits ⦃ TransformPost state right ⦄ := by
      have depth := congrArg List.length ids
      simp only [universalIds_length state.universals stateValid,
        universalIds_length before.universals valid] at depth
      apply transform_spec state right limits stateValid
      · rw [ids]; exact children.2
      · unfold TransformRoom at room ⊢
        simp only [nnfBinders, List.length_append] at room
        omega
    first
    | exact transform_binary_spec before left right false limits valid leftChecked rightChecked
    | exact transform_binary_spec before left right true limits valid leftChecked rightChecked
  | Forall binder body =>
    rw [formula_eq] at ready room
    have scalarRoom : before.universals.active.val < Usize.max := by
      unfold TransformRoom at room
      simp only [nnfBinders, List.length_cons] at room
      omega
    apply transform_universal_spec before binder body limits valid scalarRoom
    intro state stateValid ids
    have depth := congrArg List.length ids
    simp only [List.length_append, List.length_singleton, universalIds_length state.universals stateValid,
      universalIds_length before.universals valid] at depth
    apply transform_spec state body limits stateValid
    · rw [ids]; exact transformReady_universal ready
    · unfold TransformRoom at room ⊢
      simp only [nnfBinders, List.length_cons] at room
      omega
  | Exists binder body =>
    rw [formula_eq] at ready room
    apply transform_existential_spec before binder body limits valid ready
    intro state replacement target stateValid ids decoded substituted
    have depth := congrArg List.length ids
    simp only [universalIds_length state.universals stateValid,
      universalIds_length before.universals valid] at depth
    have binders := substituted_nnf_binders substituted
    have shape := substituted_nnf_shape substituted
    apply transform_spec state target limits stateValid
    · rw [ids]
      exact (transformReady_existential_substitution ready decoded substituted).1
    · unfold TransformRoom at room ⊢
      rw [binders]
      simp only [nnfBinders, List.length_cons] at room
      omega
termination_by nnfShapeSize formula
decreasing_by all_goals (simp_all only [nnfShapeSize]; omega)

theorem transform_success {before after : Transformer} {source target : Nnf} {limits : Limits}
    (valid : UniversalValid before.universals)
    (ready : TransformReady (universalIds before.universals) source)
    (room : TransformRoom before source)
    (success : Transformer.transform before source limits = .ok (.Ok target, after)) :
    TransformPost before source (.Ok target, after) := by
  have checked := transform_spec before source limits valid ready room
  rw [success] at checked
  simpa only [spec_ok] using checked

/-- This is a success corollary of the actual generated call. It does not
    discharge public input validation, original signature reservation or the
    source-byte encoding. One constructed extension works for every valuation. -/
theorem transform_meaning {before after : Transformer} {source target : Nnf} {limits : Limits}
    (valid : UniversalValid before.universals)
    (ready : TransformReady (universalIds before.universals) source)
    (room : TransformRoom before source)
    (success : Transformer.transform before source limits = .ok (.Ok target, after))
    {D : Type} [Nonempty D] (original : Fang.Interpretation D)
    (reserved : Fang.QuantifiedFOF.Skolem.FormulaBelow before.functions.val.length (decodeNnf source)) :
    ∃ extended : Fang.Interpretation D,
      Fang.QuantifiedFOF.Skolem.PreservesBelow before.functions.val.length original extended ∧
      ∀ valuation, (decodeNnf source).Holds original valuation ↔ (decodeNnf target).Holds extended valuation :=
  transformPost_meaning (transform_success valid ready room success) original reserved

end FangSkolemCore
