/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Transfer of the caller's global variable/function invariant through erasure. -/
import PipelineComposition

namespace FangQuantifiedPipeline

/-- The scope is the rectifier's global bound, including variables whose binders
    are later removed. This is not lexical scope or a predicate-arity check. -/
def InputScoped (signature : fang_fof_core.Signature) (scope : fang_fof_core.VariableScope) :
    FangBinderRemovalCore.Input → Prop
  | .Literal literal => FangScopedFof.LiteralScoped signature scope (removedLiteral literal)
  | .True | .False => True
  | .And left right | .Or left right => InputScoped signature scope left ∧ InputScoped signature scope right
  | .Forall _ body | .Exists _ body => InputScoped signature scope body

theorem erased_scoped {source : FangBinderRemovalCore.Input}
    {target : FangBinderRemovalCore.Output} (erased : FangBinderRemovalCore.Erased source target)
    (signature : fang_fof_core.Signature) (scope : fang_fof_core.VariableScope)
    (valid : InputScoped signature scope source) :
    FangScopedFof.NnfScoped signature scope (removedNnf target) := by
  induction erased with
  | literal value => exact valid
  | truth | falsity => trivial
  | and_ left right il ir | or_ left right il ir => exact ⟨il valid.1, ir valid.2⟩
  | forall_ child ih => exact ih valid

theorem remove_universals_scoped {source : FangBinderRemovalCore.Input}
    {limits : fang_binder_removal_core.Limits} {result : fang_binder_removal_core.Removed}
    (success : fang_binder_removal_core.remove_universals source limits = .ok (.Ok result))
    (signature : fang_fof_core.Signature) (scope : fang_fof_core.VariableScope)
    (valid : InputScoped signature scope source) :
    FangScopedFof.NnfScoped signature scope (removedNnf result.formula) :=
  erased_scoped (FangBinderRemovalCore.remove_universals_success success).1 signature scope valid

/-- The precondition now belongs to the Skolem output entering the remover.
    Deriving it from the Skolemizer's actual signature and binder witness is
    still a separate obligation. No arity or variable bound is inferred here. -/
theorem remove_clausify_input_models
    {formula : fang_skolem_core.fang_quantified_fof_core.Nnf}
    {removalLimits : fang_binder_removal_core.Limits}
    {removed : fang_binder_removal_core.Removed}
    (removal : fang_binder_removal_core.remove_universals (skolemNnf formula) removalLimits =
      .ok (.Ok removed))
    (free : List Nat)
    (safe : Fang.QuantifiedFOF.BinderRemoval.RectifiedWithin free
      (FangSkolemCore.decodeIndependentNnf formula))
    (signature : fang_fof_core.Signature) (scope : fang_fof_core.VariableScope)
    (valid : InputScoped signature scope (skolemNnf formula))
    (limits : fang_fof_core.Limits) (before : fang_fof_core.Statistics)
    (output : fang_fof_core.Preprocessed)
    (clausification : fang_fof_core.nnf_entry.clausify_nnf_from
      (removedNnf removed.formula) limits before = .ok (.Ok output))
    {D : Type} [Nonempty D] (model : Fang.Interpretation D) :
    (FangScopedFof.decodeClauses output.clauses.val).Models model ↔
      ∀ valuation, (FangSkolemCore.decodeIndependentNnf formula).Holds model valuation :=
  remove_clausify_models removal free safe signature scope
    (remove_universals_scoped removal signature scope valid) limits before output clausification model

end FangQuantifiedPipeline
