/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedFormulaValidation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

/-- The public outcome classifies validity only on Ok or Invalid. Resource says
    which structural bound stopped the operation, not whether the input is valid. -/
def PublicValidationPost (valid : Prop) (answer : core.result.Result Statistics fang_skolem_core.fang_quantified_fof_core.Error) : Prop :=
  match answer with
  | .Ok _ => valid
  | .Err (.Invalid _) => ¬ valid
  | .Err (.Resource kind) => FormulaResource kind
  | .Err (.Unsupported _) => False

theorem validate_with_scope_spec (formula : Formula) (signature : Signature)
    (scope : VariableScope) (limits : Limits) :
    validate_with_scope formula signature scope limits
      ⦃ PublicValidationPost (FormulaValid signature (OuterValid scope) formula) ⦄ := by
  unfold validate_with_scope Work.new
  simp only [Statistics.Insts.CoreDefaultDefault.default, bind_ok]
  apply spec_bind bindings_new_spec
  intro stack ⟨valid, depth, entries⟩
  apply spec_bind (validate_formula_spec formula 1#usize signature scope stack limits _ valid (by scalar_tac))
  rintro ⟨answer, afterstack, after⟩ ⟨_, _, _, checked⟩
  have same : StackFormulaValid signature scope stack formula ↔ FormulaValid signature (OuterValid scope) formula := by
    apply formulaValid_congr
    intro id
    simp [VariableValid, depth, lookupPrefix]
  simp only [Aeneas.Std.uncurry]
  cases answer with
  | Ok value =>
    simpa [PublicValidationPost, core.result.Result.Insts.CoreOpsTry.branch] using same.mp checked
  | Err error =>
    have post : PublicValidationPost (FormulaValid signature (OuterValid scope) formula) (.Err error) := by
      cases error with
      | Invalid kind => exact fun h => checked (same.mpr h)
      | Resource kind => exact checked
      | Unsupported kind => exact checked
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post

theorem validate_closed_spec (formula : Formula) (signature : Signature) (limits : Limits) :
    validate formula signature limits
      ⦃ PublicValidationPost (FormulaValid signature (fun _ => False) formula) ⦄ := by
  exact validate_with_scope_spec formula signature .Ground limits

end FangSkolemEmbeddedCore
