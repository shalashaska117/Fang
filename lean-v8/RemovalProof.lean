/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RemovalContract

open Aeneas Aeneas.Std Aeneas.Std.WP Result
namespace FangBinderRemovalCore
open fang_binder_removal_core

theorem remove_spec (source : Input) (depth : Usize) (limits : Limits) (before : Statistics) :
    remove source depth limits before ⦃ RemovalPost source limits before ⦄ := by
  induction source generalizing depth before with
  | Literal literal =>
    unfold remove
    apply spec_bind (increment_spec before.operations limits.max_operations .Operations)
    intro tick checked
    unfold IncrementPost at checked
    split at checked
    next available =>
      obtain ⟨operation, rfl, operation_eq⟩ := checked
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
      split
      next tooDeep =>
        simp only [spec_ok]
        apply resource_post
        simp only [Counters]
        omega
      next withinDepth =>
        have depthBound : depth.val ≤ 64 := by
          simp only [core.cmp.impls.OrdUsize.min] at withinDepth
          split at withinDepth <;> scalar_tac
        apply spec_bind (increment_spec before.output_nodes limits.max_output_nodes .OutputNodes)
        intro allocation allocated
        unfold IncrementPost at allocated
        split at allocated
        next room =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
          simp only [bind_ok, spec_ok, RemovalPost]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Counters]; omega
          · exact .literal literal
          · simp only [inputNodes]; omega
          · simp only [outputNodes]; omega
        next full =>
          rw [allocated]
          have post := resource_post (.Literal literal) limits before { before with operations := operation }
            .OutputNodes (by simp only [Counters]; omega)
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    next exhausted =>
      rw [checked]
      have post := resource_post (.Literal literal) limits before before .Operations (counters_refl _ _)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  | True =>
    unfold remove
    apply spec_bind (increment_spec before.operations limits.max_operations .Operations)
    intro tick checked
    unfold IncrementPost at checked
    split at checked
    next available =>
      obtain ⟨operation, rfl, operation_eq⟩ := checked
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
      split
      next tooDeep =>
        simp only [spec_ok]
        apply resource_post
        simp only [Counters]
        omega
      next withinDepth =>
        have depthBound : depth.val ≤ 64 := by
          simp only [core.cmp.impls.OrdUsize.min] at withinDepth
          split at withinDepth <;> scalar_tac
        apply spec_bind (increment_spec before.output_nodes limits.max_output_nodes .OutputNodes)
        intro allocation allocated
        unfold IncrementPost at allocated
        split at allocated
        next room =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
          simp only [bind_ok, spec_ok, RemovalPost]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Counters]; omega
          · exact .truth
          · simp only [inputNodes]; omega
          · simp only [outputNodes]; omega
        next full =>
          rw [allocated]
          have post := resource_post (.True) limits before { before with operations := operation }
            .OutputNodes (by simp only [Counters]; omega)
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    next exhausted =>
      rw [checked]
      have post := resource_post (.True) limits before before .Operations (counters_refl _ _)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  | False =>
    unfold remove
    apply spec_bind (increment_spec before.operations limits.max_operations .Operations)
    intro tick checked
    unfold IncrementPost at checked
    split at checked
    next available =>
      obtain ⟨operation, rfl, operation_eq⟩ := checked
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
      split
      next tooDeep =>
        simp only [spec_ok]
        apply resource_post
        simp only [Counters]
        omega
      next withinDepth =>
        have depthBound : depth.val ≤ 64 := by
          simp only [core.cmp.impls.OrdUsize.min] at withinDepth
          split at withinDepth <;> scalar_tac
        apply spec_bind (increment_spec before.output_nodes limits.max_output_nodes .OutputNodes)
        intro allocation allocated
        unfold IncrementPost at allocated
        split at allocated
        next room =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
          simp only [bind_ok, spec_ok, RemovalPost]
          refine ⟨?_, ?_, ?_, ?_⟩
          · simp only [Counters]; omega
          · exact .falsity
          · simp only [inputNodes]; omega
          · simp only [outputNodes]; omega
        next full =>
          rw [allocated]
          have post := resource_post (.False) limits before { before with operations := operation }
            .OutputNodes (by simp only [Counters]; omega)
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    next exhausted =>
      rw [checked]
      have post := resource_post (.False) limits before before .Operations (counters_refl _ _)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  | And left right ihl ihr =>
    unfold remove
    apply spec_bind (increment_spec before.operations limits.max_operations .Operations)
    intro tick checked
    unfold IncrementPost at checked
    split at checked
    next available =>
      obtain ⟨operation, rfl, operation_eq⟩ := checked
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
      split
      next tooDeep =>
        simp only [spec_ok]
        apply resource_post
        simp only [Counters]
        omega
      next withinDepth =>
        have depthBound : depth.val ≤ 64 := by
          simp only [core.cmp.impls.OrdUsize.min] at withinDepth
          split at withinDepth <;> scalar_tac
        apply spec_bind (increment_spec before.output_nodes limits.max_output_nodes .OutputNodes)
        intro allocation allocated
        unfold IncrementPost at allocated
        split at allocated
        next room =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
          simp only [bind_ok]
          apply spec_bind (Usize.add_spec (x := depth) (y := 1#usize) (by scalar_tac))
          intro deeper _
          apply spec_bind (ihl deeper { operations := operation, output_nodes := nodes })
          rintro ⟨leftAnswer, middle⟩ ⟨leftCounters, leftOutcome⟩
          dsimp only at leftCounters leftOutcome
          simp only [Aeneas.Std.uncurry]
          have initial : Counters limits before { operations := operation, output_nodes := nodes } := by
            simp only [Counters]; omega
          have firstCounters := counters_trans initial leftCounters
          cases leftAnswer with
          | Err error =>
            have post : RemovalPost (.And left right) limits before (.Err error, middle) := by
              refine ⟨firstCounters, ?_⟩
              cases error with
              | Resource _ => trivial
              | ResidualExistential id => exact Or.inl leftOutcome
            simpa [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
          | Ok l =>
            simp only [bind_ok]
            apply spec_bind (ihr deeper middle)
            rintro ⟨rightAnswer, after⟩ ⟨rightCounters, rightOutcome⟩
            dsimp only at rightCounters rightOutcome
            simp only [Aeneas.Std.uncurry]
            have finalCounters := counters_trans firstCounters rightCounters
            cases rightAnswer with
            | Err error =>
              have post : RemovalPost (.And left right) limits before (.Err error, after) := by
                refine ⟨finalCounters, ?_⟩
                cases error with
                | Resource _ => trivial
                | ResidualExistential id => exact Or.inr rightOutcome
              simpa [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
            | Ok r =>
              obtain ⟨leftErased, leftOps, leftNodes⟩ := leftOutcome
              obtain ⟨rightErased, rightOps, rightNodes⟩ := rightOutcome
              simp only [bind_ok, spec_ok, RemovalPost]
              refine ⟨finalCounters, ?_, ?_, ?_⟩
              · exact .and_ leftErased rightErased
              · simp only [inputNodes]; omega
              · simp only [outputNodes]; omega
        next full =>
          rw [allocated]
          have post := resource_post (.And left right) limits before { before with operations := operation }
            .OutputNodes (by simp only [Counters]; omega)
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    next exhausted =>
      rw [checked]
      have post := resource_post (.And left right) limits before before .Operations (counters_refl _ _)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  | Or left right ihl ihr =>
    unfold remove
    apply spec_bind (increment_spec before.operations limits.max_operations .Operations)
    intro tick checked
    unfold IncrementPost at checked
    split at checked
    next available =>
      obtain ⟨operation, rfl, operation_eq⟩ := checked
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
      split
      next tooDeep =>
        simp only [spec_ok]
        apply resource_post
        simp only [Counters]
        omega
      next withinDepth =>
        have depthBound : depth.val ≤ 64 := by
          simp only [core.cmp.impls.OrdUsize.min] at withinDepth
          split at withinDepth <;> scalar_tac
        apply spec_bind (increment_spec before.output_nodes limits.max_output_nodes .OutputNodes)
        intro allocation allocated
        unfold IncrementPost at allocated
        split at allocated
        next room =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
          simp only [bind_ok]
          apply spec_bind (Usize.add_spec (x := depth) (y := 1#usize) (by scalar_tac))
          intro deeper _
          apply spec_bind (ihl deeper { operations := operation, output_nodes := nodes })
          rintro ⟨leftAnswer, middle⟩ ⟨leftCounters, leftOutcome⟩
          dsimp only at leftCounters leftOutcome
          simp only [Aeneas.Std.uncurry]
          have initial : Counters limits before { operations := operation, output_nodes := nodes } := by
            simp only [Counters]; omega
          have firstCounters := counters_trans initial leftCounters
          cases leftAnswer with
          | Err error =>
            have post : RemovalPost (.Or left right) limits before (.Err error, middle) := by
              refine ⟨firstCounters, ?_⟩
              cases error with
              | Resource _ => trivial
              | ResidualExistential id => exact Or.inl leftOutcome
            simpa [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
          | Ok l =>
            simp only [bind_ok]
            apply spec_bind (ihr deeper middle)
            rintro ⟨rightAnswer, after⟩ ⟨rightCounters, rightOutcome⟩
            dsimp only at rightCounters rightOutcome
            simp only [Aeneas.Std.uncurry]
            have finalCounters := counters_trans firstCounters rightCounters
            cases rightAnswer with
            | Err error =>
              have post : RemovalPost (.Or left right) limits before (.Err error, after) := by
                refine ⟨finalCounters, ?_⟩
                cases error with
                | Resource _ => trivial
                | ResidualExistential id => exact Or.inr rightOutcome
              simpa [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
            | Ok r =>
              obtain ⟨leftErased, leftOps, leftNodes⟩ := leftOutcome
              obtain ⟨rightErased, rightOps, rightNodes⟩ := rightOutcome
              simp only [bind_ok, spec_ok, RemovalPost]
              refine ⟨finalCounters, ?_, ?_, ?_⟩
              · exact .or_ leftErased rightErased
              · simp only [inputNodes]; omega
              · simp only [outputNodes]; omega
        next full =>
          rw [allocated]
          have post := resource_post (.Or left right) limits before { before with operations := operation }
            .OutputNodes (by simp only [Counters]; omega)
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    next exhausted =>
      rw [checked]
      have post := resource_post (.Or left right) limits before before .Operations (counters_refl _ _)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  | Forall id body ih =>
    unfold remove
    apply spec_bind (increment_spec before.operations limits.max_operations .Operations)
    intro tick checked
    unfold IncrementPost at checked
    split at checked
    next available =>
      obtain ⟨operation, rfl, operation_eq⟩ := checked
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
      split
      next tooDeep =>
        simp only [spec_ok]
        apply resource_post
        simp only [Counters]
        omega
      next withinDepth =>
        have depthBound : depth.val ≤ 64 := by
          simp only [core.cmp.impls.OrdUsize.min] at withinDepth
          split at withinDepth <;> scalar_tac
        apply spec_bind (Usize.add_spec (x := depth) (y := 1#usize) (by scalar_tac))
        intro deeper _
        apply spec_mono (ih deeper { before with operations := operation })
        rintro ⟨answer, after⟩ ⟨counters, outcome⟩
        refine ⟨counters_trans (by simp only [Counters]; omega) counters, ?_⟩
        cases answer with
        | Ok target =>
          obtain ⟨erased, operations, nodes⟩ := outcome
          exact ⟨.forall_ erased, by simp only [inputNodes]; dsimp only at operations; omega, nodes⟩
        | Err error => exact outcome
    next exhausted =>
      rw [checked]
      have post := resource_post (.Forall id body) limits before before .Operations (counters_refl _ _)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  | Exists id body ih =>
    unfold remove
    apply spec_bind (increment_spec before.operations limits.max_operations .Operations)
    intro tick checked
    unfold IncrementPost at checked
    split at checked
    next available =>
      obtain ⟨operation, rfl, operation_eq⟩ := checked
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
      split
      next tooDeep =>
        simp only [spec_ok]
        apply resource_post
        simp only [Counters]
        omega
      next withinDepth =>
        have depthBound : depth.val ≤ 64 := by
          simp only [core.cmp.impls.OrdUsize.min] at withinDepth
          split at withinDepth <;> scalar_tac
        simp only [spec_ok]
        refine ⟨?_, Or.inl rfl⟩
        simp only [Counters]; omega
    next exhausted =>
      rw [checked]
      have post := resource_post (.Exists id body) limits before before .Operations (counters_refl _ _)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post

end FangBinderRemovalCore
