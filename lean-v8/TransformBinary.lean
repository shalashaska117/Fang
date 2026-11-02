/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Composition of the actual transformer's two ordered recursive calls. -/
import TransformLeaves

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

/-- Recursive contracts are explicit premises here. The later whole-call proof
    must discharge them with its decreasing formula-shape measure. -/
theorem transform_binary_spec (before : Transformer) (left right : Nnf) (disjunction : Bool)
    (limits : Limits) (valid : UniversalValid before.universals)
    (leftChecked : ∀ state : Transformer, UniversalValid state.universals →
      universalIds state.universals = universalIds before.universals →
      Transformer.transform state left limits ⦃ TransformPost state left ⦄)
    (rightChecked : ∀ state : Transformer, UniversalValid state.universals →
      universalIds state.universals = universalIds before.universals →
      Transformer.transform state right limits ⦃ TransformPost state right ⦄) :
    Transformer.transform before (if disjunction then .Or left right else .And left right) limits
      ⦃ TransformPost before (if disjunction then .Or left right else .And left right) ⦄ := by
  cases disjunction <;>
    (unfold Transformer.transform
     apply spec_bind (tick_spec before.work limits)
     intro answer ticked
     unfold TickAnswer at ticked
     split at ticked
     next fits =>
       obtain ⟨operation, rfl, operation_eq⟩ := ticked
       simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
       apply spec_bind (allocate_spec _ 1#usize limits)
       intro answer allocated
       unfold AllocationAnswer at allocated
       split at allocated
       next storageFits =>
         obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
         simp only [Aeneas.Std.uncurry, bind_ok]
         let advanced : Transformer := { before with work := { statistics := {
           operations := operation, allocated_nodes := nodes } } }
         apply spec_bind (leftChecked advanced valid rfl)
         rintro ⟨leftResult, intermediate⟩ ⟨leftValid, leftFrame, leftDeclaration, leftOperations, leftOutcome⟩
         dsimp only [advanced] at leftValid leftFrame leftDeclaration leftOperations leftOutcome
         simp only [Aeneas.Std.uncurry]
         cases leftResult with
         | Err error =>
           have post : TransformPost before (.And left right) (.Err error, intermediate) := by
             exact ⟨leftValid, leftFrame, leftDeclaration, by dsimp only; omega, leftOutcome⟩
           simpa [TransformPost, core.result.Result.Insts.CoreOpsTry.branch,
             core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
         | Ok l =>
           simp only [bind_ok]
           apply spec_bind (rightChecked intermediate leftValid (universalFrame_ids leftFrame))
           rintro ⟨rightResult, after⟩ ⟨rightValid, rightFrame, rightDeclaration, rightOperations, rightOutcome⟩
           dsimp only at rightValid rightFrame rightDeclaration rightOperations rightOutcome
           simp only [Aeneas.Std.uncurry]
           have frame := universalFrame_trans leftFrame rightFrame
           have declaration := rightDeclaration.trans leftDeclaration
           have operations : before.work.statistics.operations.val ≤ after.work.statistics.operations.val := by omega
           cases rightResult with
           | Err error =>
             have post : TransformPost before (.And left right) (.Err error, after) :=
               ⟨rightValid, frame, declaration, operations, rightOutcome⟩
             simpa [TransformPost, core.result.Result.Insts.CoreOpsTry.branch,
               core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
           | Ok r =>
             simp only [bind_ok, spec_ok, TransformPost]
             refine ⟨rightValid, frame, declaration, operations, ?_⟩
             rw [universalFrame_ids leftFrame] at rightOutcome
             first
             | exact .conjunction leftOutcome rightOutcome
             | exact .disjunction leftOutcome rightOutcome
       next storageExceeded =>
         rw [allocated]
         have post := transformPost_resource before (.And left right)
           { statistics := { before.work.statistics with operations := operation } } .StoredNodes valid
           (by dsimp only; omega) (Or.inr (Or.inl rfl))
         simpa [TransformPost, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
     next exceeded =>
       rw [ticked]
       have post := transformPost_resource before (.And left right) before.work .Operations valid
         (Nat.le_refl _) (Or.inl rfl)
       simpa [TransformPost, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post)

end FangSkolemCore
