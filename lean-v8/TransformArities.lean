/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Function-signature preservation by the actual generated Skolem transformer. -/
import TransformArityBranches

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

theorem transform_arities_spec (before : Transformer) (formula : Nnf) (limits : Limits)
    (valid : UniversalValid before.universals)
    (ready : TransformReady (universalIds before.universals) formula)
    (room : TransformRoom before formula) (arities : NnfArities before.functions formula) :
    Transformer.transform before formula limits ⦃ TransformArityPost before ⦄ := by
  cases formula_eq : formula with
  | Literal literal =>
    rw [formula_eq] at arities
    exact transform_literal_arities before literal limits arities
  | True => exact transform_constant_arities before true limits
  | False => exact transform_constant_arities before false limits
  | And left right | Or left right =>
    rw [formula_eq] at ready room arities
    have children : TransformReady (universalIds before.universals) left ∧
        TransformReady (universalIds before.universals) right := transformReady_and ready
    have leftChecked (state : Transformer) (stateValid : UniversalValid state.universals)
        (ids : universalIds state.universals = universalIds before.universals)
        (typed : NnfArities state.functions left) :
        Transformer.transform state left limits ⦃ fun answer =>
          TransformPost state left answer ∧ TransformArityPost state answer ⦄ := by
      have depth := congrArg List.length ids
      simp only [universalIds_length state.universals stateValid,
        universalIds_length before.universals valid] at depth
      have childReady : TransformReady (universalIds state.universals) left := by rw [ids]; exact children.1
      have childRoom : TransformRoom state left := by
        unfold TransformRoom at room ⊢
        simp only [nnfBinders, List.length_append] at room
        omega
      exact spec_and (transform_spec state left limits stateValid childReady childRoom)
        (transform_arities_spec state left limits stateValid childReady childRoom typed)
    have rightChecked (state : Transformer) (stateValid : UniversalValid state.universals)
        (ids : universalIds state.universals = universalIds before.universals)
        (typed : NnfArities state.functions right) :
        Transformer.transform state right limits ⦃ fun answer =>
          TransformPost state right answer ∧ TransformArityPost state answer ⦄ := by
      have depth := congrArg List.length ids
      simp only [universalIds_length state.universals stateValid,
        universalIds_length before.universals valid] at depth
      have childReady : TransformReady (universalIds state.universals) right := by rw [ids]; exact children.2
      have childRoom : TransformRoom state right := by
        unfold TransformRoom at room ⊢
        simp only [nnfBinders, List.length_append] at room
        omega
      exact spec_and (transform_spec state right limits stateValid childReady childRoom)
        (transform_arities_spec state right limits stateValid childReady childRoom typed)
    first
    | exact transform_binary_arities before left right false limits valid arities leftChecked rightChecked
    | exact transform_binary_arities before left right true limits valid arities leftChecked rightChecked
  | Forall binder body =>
    rw [formula_eq] at ready room arities
    have scalarRoom : before.universals.active.val < Usize.max := by
      unfold TransformRoom at room
      simp only [nnfBinders, List.length_cons] at room
      omega
    apply transform_universal_arities before binder body limits valid scalarRoom arities
    intro state stateValid ids typed
    have depth := congrArg List.length ids
    simp only [List.length_append, List.length_singleton, universalIds_length state.universals stateValid,
      universalIds_length before.universals valid] at depth
    have childReady : TransformReady (universalIds state.universals) body := by
      rw [ids]; exact transformReady_universal ready
    have childRoom : TransformRoom state body := by
      unfold TransformRoom at room ⊢
      simp only [nnfBinders, List.length_cons] at room
      omega
    exact spec_and (transform_spec state body limits stateValid childReady childRoom)
      (transform_arities_spec state body limits stateValid childReady childRoom typed)
  | Exists binder body =>
    rw [formula_eq] at ready room arities
    apply transform_existential_arities before binder body limits valid arities
    intro state replacement target stateValid ids decoded substituted typed
    have depth := congrArg List.length ids
    simp only [universalIds_length state.universals stateValid,
      universalIds_length before.universals valid] at depth
    have binders := substituted_nnf_binders substituted
    have shape := substituted_nnf_shape substituted
    apply transform_arities_spec state target limits stateValid
    · rw [ids]
      exact (transformReady_existential_substitution ready decoded substituted).1
    · unfold TransformRoom at room ⊢
      rw [binders]
      simp only [nnfBinders, List.length_cons] at room
      omega
    · exact typed
termination_by nnfShapeSize formula
decreasing_by all_goals (simp_all only [nnfShapeSize]; omega)

/-- Original function IDs keep their exact arities. Every returned term and
    every recorded Skolem dependency list agrees with the extended table.
    Predicate arities and variable bounds are separate obligations. -/
theorem transform_arities_success {before after : Transformer} {source target : Nnf} {limits : Limits}
    (valid : UniversalValid before.universals)
    (ready : TransformReady (universalIds before.universals) source)
    (room : TransformRoom before source) (arities : NnfArities before.functions source)
    (success : Transformer.transform before source limits = .ok (.Ok target, after)) :
    FunctionPrefix before.functions after.functions ∧ NnfArities after.functions target ∧
      (IntroducedArities before.functions before.introduced →
        IntroducedArities after.functions after.introduced) := by
  have checked := transform_arities_spec before source limits valid ready room arities
  rw [success] at checked
  simpa only [spec_ok, TransformArityPost] using checked

end FangSkolemCore
