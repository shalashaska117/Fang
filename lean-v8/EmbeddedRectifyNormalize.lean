/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedNormalize
import EmbeddedRectifySemantics
import EmbeddedRectifyValidity

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

theorem rectify_closed_semantics (formula : Formula) (signature : Signature) (limits : Limits)
    {D : Type} (model : Fang.Interpretation D) (valuation : Nat → D) :
    rectify_closed formula signature limits ⦃ answer =>
      match answer with
      | .Ok output => (decodeFormula output.formula).Holds model valuation ↔
          (decodeFormula formula).Holds model valuation
      | .Err _ => True ⦄ := by
  apply spec_mono (rectify_closed_spec formula signature limits)
  intro answer checked
  cases answer with
  | Err error => trivial
  | Ok output =>
    exact (rectified_holds model checked.2.1
      (by intro id fresh impossible; cases impossible) valuation valuation
      (by intro id fresh impossible; cases impossible)).symm

def RectifyNormalizePost (formula : Formula) (positive : Bool) (signature : Signature)
    (answer : core.result.Result Normalized fang_skolem_core.fang_quantified_fof_core.Error) : Prop :=
  match answer with
  | .Ok output => FormulaValid signature (fun _ => False) formula ∧
      ∃ target count, RectifiedFormula (fun _ => none) 0 formula target count ∧
        decodeNnf output.formula = (decodeFormula target).nnf positive
  | .Err (.Invalid _) => ¬ FormulaValid signature (fun _ => False) formula
  | .Err (.Resource kind) => FormulaResource kind ∨ CopyResource kind
  | .Err (.Unsupported _) => False

/-- The public composition calls the actual rectifier and the same normalizer. -/
theorem rectify_normalize_closed_spec (formula : Formula) (positive : Bool)
    (signature : Signature) (limits : Limits) :
    rectify_normalize_closed formula positive signature limits
      ⦃ RectifyNormalizePost formula positive signature ⦄ := by
  unfold rectify_normalize_closed
  apply spec_bind (rectify_closed_spec formula signature limits)
  intro answer checked
  cases answer with
  | Err error =>
    have post : RectifyNormalizePost formula positive signature (.Err error) := by
      cases error <;> exact checked
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  | Ok rectified =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (normalize_formula_spec rectified.formula signature (fun _ => True)
      (rectified_signature checked.2.1 signature (fun _ => False) checked.1)
      positive limits {statistics := rectified.statistics})
    rintro ⟨result, finalWork⟩ ⟨_, normalized⟩
    dsimp only at normalized
    simp only [Aeneas.Std.uncurry]
    cases result with
    | Err error =>
      have post : RectifyNormalizePost formula positive signature (.Err error) := by
        cases error with
        | Invalid kind => exact False.elim normalized
        | Unsupported kind => exact normalized
        | Resource kind => exact Or.inr normalized
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok target =>
      simp only [bind_ok, spec_ok, RectifyNormalizePost]
      exact ⟨checked.1, rectified.formula, rectified.binder_count.val, checked.2.1, normalized⟩

/-- Actual rectification followed by actual NNF preserves the original formula's meaning. -/
theorem rectify_normalize_closed_semantics (formula : Formula) (positive : Bool)
    (signature : Signature) (limits : Limits) {D : Type}
    (model : Fang.Interpretation D) (valuation : Nat → D) :
    rectify_normalize_closed formula positive signature limits ⦃ answer =>
      match answer with
      | .Ok output => (decodeNnf output.formula).Holds model valuation ↔
          Fang.GroundFOF.signed positive ((decodeFormula formula).Holds model valuation)
      | .Err _ => True ⦄ := by
  apply spec_mono (rectify_normalize_closed_spec formula positive signature limits)
  intro answer checked
  cases answer with
  | Err error => trivial
  | Ok output =>
    obtain ⟨_, target, count, renamed, normalized⟩ := checked
    have equivalent := rectified_holds model renamed
      (by intro id fresh impossible; cases impossible) valuation valuation
      (by intro id fresh impossible; cases impossible)
    dsimp only
    rw [normalized]
    simpa only [← equivalent] using Fang.QuantifiedFOF.nnf_holds model valuation (decodeFormula target) positive

end FangSkolemEmbeddedCore
