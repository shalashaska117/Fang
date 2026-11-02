/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft public-call readiness from the actual rectifier/NNF witness. -/
import PublicPreparation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

/-- The scalar count remains in this proof witness even though the executable
    Normalized result does not expose it. Error classification is covered by
    rectify_normalize_closed_spec; this success-only postcondition adds a witness. -/
def NormalizedWitness (source : Formula) (positive : Bool) (signature : Signature)
    (answer : core.result.Result Normalized fang_skolem_core.fang_quantified_fof_core.Error) : Prop :=
  match answer with
  | .Ok output => FormulaValid signature (fun _ => False) source ∧
      ∃ (target : Formula) (count : U32), RectifiedFormula (fun _ => none) 0 source target count.val ∧
        decodeNnf output.formula = (decodeFormula target).nnf positive
  | .Err _ => True

theorem normalized_witness_spec (source : Formula) (positive : Bool)
    (signature : Signature) (limits : Limits) :
    rectify_normalize_closed source positive signature limits
      ⦃ NormalizedWitness source positive signature ⦄ := by
  unfold rectify_normalize_closed
  apply spec_bind (rectify_closed_spec source signature limits)
  intro answer checked
  cases answer with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, NormalizedWitness]
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
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, NormalizedWitness]
    | Ok target =>
      simp only [bind_ok, spec_ok, NormalizedWitness]
      exact ⟨checked.1, rectified.formula, rectified.binder_count, checked.2.1, normalized⟩

end FangSkolemEmbeddedCore

namespace FangSkolemCore
open fang_skolem_core

theorem normalized_ready {source target : fang_quantified_fof_core.Formula} {count : U32}
    {formula : fang_quantified_fof_core.Nnf} {positive : Bool}
    (renamed : FangSkolemEmbeddedCore.RectifiedFormula (fun _ => none) 0 source target count.val)
    (normalized : FangSkolemEmbeddedCore.decodeNnf formula =
      (FangSkolemEmbeddedCore.decodeFormula target).nnf positive) :
    TransformReady [] formula ∧ (nnfBinders formula).length = count.val := by
  have ids : (nnfBinders formula).map (fun id => id.val) =
      (FangSkolemEmbeddedCore.binderIds target).map (fun id => id.val) := by
    rw [← decoded_nnf_binders, ← decodeIndependent_binders, ← embedded_decodeNnf,
      normalized, independent_nnf_binders, embedded_formula_binders]
  have within : (decodeNnf formula).Within [] := by
    apply (decodeIndependent_within formula []).mp
    rw [← embedded_decodeNnf, normalized]
    exact Fang.QuantifiedFOF.nnf_within _ _ [] (FangSkolemEmbeddedCore.rectified_closed renamed)
  have unique : (nnfBinders formula).Nodup := by
    apply List.Nodup.of_map (f := fun id : U32 => id.val)
    rw [ids]
    exact variableValues_nodup _ (FangSkolemEmbeddedCore.rectified_binders_unique renamed)
  have length := congrArg List.length ids
  simp only [List.length_map, FangSkolemEmbeddedCore.binderIds_length] at length
  have counter := FangSkolemEmbeddedCore.rectified_counter renamed
  exact ⟨⟨within, unique, by simp⟩, by omega⟩

theorem normalized_room {source target : fang_quantified_fof_core.Formula} {count : U32}
    {formula : fang_quantified_fof_core.Nnf} {positive : Bool} (before : Transformer)
    (empty : before.universals.active.val = 0)
    (renamed : FangSkolemEmbeddedCore.RectifiedFormula (fun _ => none) 0 source target count.val)
    (normalized : FangSkolemEmbeddedCore.decodeNnf formula =
      (FangSkolemEmbeddedCore.decodeFormula target).nnf positive) :
    TransformRoom before formula := by
  have length := (normalized_ready renamed normalized).2
  simp only [TransformRoom, empty, Nat.zero_add, length]
  scalar_tac

theorem actual_normalized_ready {source : fang_quantified_fof_core.Formula}
    {positive : Bool} {signature : fang_quantified_fof_core.Signature}
    {limits : fang_quantified_fof_core.Limits} {output : fang_quantified_fof_core.Normalized}
    (success : fang_quantified_fof_core.rectify_normalize_closed source positive signature limits = .ok (.Ok output)) :
    TransformReady [] output.formula ∧ ∀ before : Transformer,
      before.universals.active.val = 0 → TransformRoom before output.formula := by
  have checked := FangSkolemEmbeddedCore.normalized_witness_spec source positive signature limits
  rw [success] at checked
  simp only [spec_ok, FangSkolemEmbeddedCore.NormalizedWitness] at checked
  obtain ⟨_, target, count, renamed, normalized⟩ := checked
  exact ⟨(normalized_ready renamed normalized).1,
    fun before empty => normalized_room before empty renamed normalized⟩

end FangSkolemCore
