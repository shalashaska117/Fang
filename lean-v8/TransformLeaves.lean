/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Direct contracts for the actual transformer's literal and Boolean leaves. -/
import TransformContract

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

theorem skolemized_literal (universals : List Nat) (first : Nat) (literal : fang.syntax.Literal) :
    Fang.QuantifiedFOF.Skolem.Skolemized universals first
      (literalFormula literal) (literalFormula literal) first := by
  unfold literalFormula
  cases literal.positive with
  | false => exact .negation (.atom _ _ _)
  | true => exact .atom _ _ _

theorem transform_literal_spec (before : Transformer) (literal : fang.syntax.Literal) (limits : Limits)
    (valid : UniversalValid before.universals) :
    Transformer.transform before (.Literal literal) limits ⦃ TransformPost before (.Literal literal) ⦄ := by
  unfold Transformer.transform
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
      apply spec_bind (copy_literal_spec literal limits _)
      rintro ⟨result, after⟩ ⟨monotone, outcome⟩
      dsimp only at monotone outcome
      simp only [Aeneas.Std.uncurry]
      cases result with
      | Ok value =>
        subst value
        simp only [bind_ok, spec_ok, TransformPost]
        exact ⟨valid, universalFrame_refl _, trivial, by omega, skolemized_literal _ _ _⟩
      | Err error =>
        have post : TransformPost before (.Literal literal) (.Err error, { before with work := after }) := by
          refine ⟨valid, universalFrame_refl _, rfl, by dsimp only; omega, ?_⟩
          cases error with
          | Core kind => exact outcome
          | Resource kind => exact copyResource_transform outcome
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    next storageExceeded =>
      rw [allocated]
      have post := transformPost_resource before (.Literal literal)
        { statistics := { before.work.statistics with operations := operation } } .StoredNodes valid
        (by dsimp only; omega) (Or.inr (Or.inl rfl))
      simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  next exceeded =>
    rw [ticked]
    have post := transformPost_resource before (.Literal literal) before.work .Operations valid
      (Nat.le_refl _) (Or.inl rfl)
    simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post

theorem transform_constant_spec (before : Transformer) (value : Bool) (limits : Limits)
    (valid : UniversalValid before.universals) :
    Transformer.transform before (if value then .True else .False) limits
      ⦃ TransformPost before (if value then .True else .False) ⦄ := by
  cases value <;>
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
         simp only [Aeneas.Std.uncurry, bind_ok, spec_ok, TransformPost]
         refine ⟨valid, universalFrame_refl _, trivial, by omega, ?_⟩
         first | exact .truth _ _ | exact .falsity _ _
       next storageExceeded =>
         rw [allocated]
         have post := transformPost_resource before .False
           { statistics := { before.work.statistics with operations := operation } } .StoredNodes valid
           (by dsimp only; omega) (Or.inr (Or.inl rfl))
         simpa [TransformPost, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
     next exceeded =>
       rw [ticked]
       have post := transformPost_resource before .False before.work .Operations valid (Nat.le_refl _) (Or.inl rfl)
       simpa [TransformPost, Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
         core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post)

end FangSkolemCore
