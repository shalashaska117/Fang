/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Successful generated calls compose under the stated caller invariants. -/
import SkolemRemovalMap
import RemovalClausifierMap

namespace FangQuantifiedPipeline

/-- This theorem concerns the actual removal and clausification calls. The
    low-level clausifier's scope/signature invariant is an explicit premise. -/
theorem remove_clausify_models
    {formula : fang_skolem_core.fang_quantified_fof_core.Nnf}
    {removalLimits : fang_binder_removal_core.Limits}
    {removed : fang_binder_removal_core.Removed}
    (removal : fang_binder_removal_core.remove_universals (skolemNnf formula) removalLimits =
      .ok (.Ok removed))
    (free : List Nat)
    (safe : Fang.QuantifiedFOF.BinderRemoval.RectifiedWithin free
      (FangSkolemCore.decodeIndependentNnf formula))
    (signature : fang_fof_core.Signature) (scope : fang_fof_core.VariableScope)
    (valid : FangScopedFof.NnfScoped signature scope (removedNnf removed.formula))
    (limits : fang_fof_core.Limits) (before : fang_fof_core.Statistics)
    (output : fang_fof_core.Preprocessed)
    (clausification : fang_fof_core.nnf_entry.clausify_nnf_from
      (removedNnf removed.formula) limits before = .ok (.Ok output))
    {D : Type} [Nonempty D] (model : Fang.Interpretation D) :
    (FangScopedFof.decodeClauses output.clauses.val).Models model ↔
      ∀ valuation, (FangSkolemCore.decodeIndependentNnf formula).Holds model valuation := by
  have erased := FangBinderRemovalCore.remove_universals_models model removal free
    (by simpa only [skolemNnf_decode] using safe)
  have clauses := FangScopedFof.clausify_nnf_from_models _ signature scope valid limits before
    output clausification model
  rw [removedNnf_decode] at clauses
  rw [skolemNnf_decode] at erased
  exact clauses.trans erased.symm

/-- One model extension connects a successful actual Skolem transform to the
    actual resulting clause list. Public validation, a shared whole-problem
    extension, wrapper control flow and source bytes are separate obligations. -/
theorem transform_remove_clausify_models
    {state final : fang_skolem_core.Transformer}
    {source target : fang_skolem_core.fang_quantified_fof_core.Nnf}
    {skolemLimits : fang_skolem_core.Limits}
    (stack : FangSkolemCore.UniversalValid state.universals)
    (ready : FangSkolemCore.TransformReady (FangSkolemCore.universalIds state.universals) source)
    (room : FangSkolemCore.TransformRoom state source)
    (transformed : fang_skolem_core.Transformer.transform state source skolemLimits =
      .ok (.Ok target, final))
    {removalLimits : fang_binder_removal_core.Limits}
    {removed : fang_binder_removal_core.Removed}
    (removal : fang_binder_removal_core.remove_universals (skolemNnf target) removalLimits =
      .ok (.Ok removed))
    (signature : fang_fof_core.Signature) (scope : fang_fof_core.VariableScope)
    (valid : FangScopedFof.NnfScoped signature scope (removedNnf removed.formula))
    (limits : fang_fof_core.Limits) (before : fang_fof_core.Statistics)
    (output : fang_fof_core.Preprocessed)
    (clausification : fang_fof_core.nnf_entry.clausify_nnf_from
      (removedNnf removed.formula) limits before = .ok (.Ok output))
    {D : Type} [Nonempty D] (original : Fang.Interpretation D)
    (reserved : Fang.QuantifiedFOF.Skolem.FormulaBelow state.functions.val.length
      (FangSkolemCore.decodeNnf source)) :
    ∃ extended : Fang.Interpretation D,
      Fang.QuantifiedFOF.Skolem.PreservesBelow state.functions.val.length original extended ∧
      ((FangScopedFof.decodeClauses output.clauses.val).Models extended ↔
        ∀ valuation, (FangSkolemCore.decodeNnf source).Holds original valuation) := by
  obtain ⟨extended, preserves, meaning⟩ :=
    FangSkolemCore.transform_meaning stack ready room transformed original reserved
  refine ⟨extended, preserves, ?_⟩
  have safe := FangSkolemCore.transform_output_rectified stack ready room transformed
  have composed := remove_clausify_models removal _ safe signature scope valid limits before
    output clausification extended
  apply composed.trans
  apply forall_congr'
  intro valuation
  exact (FangSkolemCore.decodeIndependent_holds extended target valuation).trans
    (meaning valuation).symm

end FangQuantifiedPipeline
