/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedRectification

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

def PublicRectificationPost (signature : Signature) (source : Formula)
    (answer : core.result.Result Rectified fang_skolem_core.fang_quantified_fof_core.Error) : Prop :=
  match answer with
  | .Ok value =>
      FormulaValid signature (fun _ => False) source ∧
      RectifiedFormula (fun _ => none) 0 source value.formula value.binder_count.val ∧
      value.binder_count.val = binderCount source ∧
      (binderIds value.formula).map UScalar.val = List.range' 0 (binderCount source) ∧
      (binderIds value.formula).Nodup
  | .Err (.Invalid _) => ¬ FormulaValid signature (fun _ => False) source
  | .Err (.Resource kind) => FormulaResource kind ∨ CopyResource kind
  | .Err (.Unsupported _) => False

theorem rectify_closed_spec (formula : Formula) (signature : Signature) (limits : Limits) :
    rectify_closed formula signature limits ⦃ PublicRectificationPost signature formula ⦄ := by
  unfold rectify_closed Work.new
  simp only [Statistics.Insts.CoreDefaultDefault.default, bind_ok]
  apply spec_bind bindings_new_spec
  intro stack ⟨valid, depth, entries⟩
  apply spec_bind (validate_formula_spec formula 1#usize signature .Ground stack limits _ valid (by scalar_tac))
  rintro ⟨answer, afterstack, after⟩ ⟨_, _, _, checked⟩
  have same : StackFormulaValid signature .Ground stack formula ↔ FormulaValid signature (fun _ => False) formula := by
    apply formulaValid_congr
    intro id
    simp [VariableValid, OuterValid, depth, lookupPrefix]
  simp only [Aeneas.Std.uncurry]
  cases answer with
  | Err error =>
    have post : PublicRectificationPost signature formula (.Err error) := by
      cases error with
      | Invalid kind => exact fun h => checked (same.mpr h)
      | Resource kind => exact Or.inl checked
      | Unsupported kind => exact checked
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  | Ok ignored =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (rectify_formula_spec formula signature stack 0#u32 limits after valid (by scalar_tac) checked)
    rintro ⟨result, finalstack, finalNext, finalWork⟩ ⟨_, _, _, _, renamed⟩
    dsimp only at renamed
    have resolver : StackResolver stack = fun _ => none := by
      funext id
      simp [StackResolver, depth, lookupPrefix]
    simp only [Aeneas.Std.uncurry]
    cases result with
    | Err error =>
      have post : PublicRectificationPost signature formula (.Err error) := by
        cases error with
        | Invalid kind => exact False.elim renamed
        | Unsupported kind => exact renamed
        | Resource kind =>
          rcases renamed with copy | binder
          · exact Or.inr copy
          · exact Or.inl (Or.inr (Or.inr (Or.inr binder)))
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok target =>
      rw [resolver] at renamed
      have relation : RectifiedFormula (fun _ => none) 0 formula target finalNext.val := renamed
      simp only [bind_ok, spec_ok, PublicRectificationPost]
      exact ⟨same.mp checked, relation, by simpa using (rectified_counter relation).1,
        rectified_binder_ids relation, rectified_binders_unique relation⟩

end FangSkolemEmbeddedCore
