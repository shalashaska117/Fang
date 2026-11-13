/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Actual generated substitution, including stopping at a rebinding. -/
import SubstituteLiteral

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

inductive SubstitutedNnf (binder : U32) (replacement : fang.syntax.Term) : Bool → Nnf → Nnf → Prop where
  | literalOn {source target} (related : SubstitutedLiteral binder replacement source target) :
      SubstitutedNnf binder replacement true (.Literal source) (.Literal target)
  | literalOff (literal) : SubstitutedNnf binder replacement false (.Literal literal) (.Literal literal)
  | truth (active) : SubstitutedNnf binder replacement active .True .True
  | falsity (active) : SubstitutedNnf binder replacement active .False .False
  | conjunction {active left right l r}
      (leftChild : SubstitutedNnf binder replacement active left l)
      (rightChild : SubstitutedNnf binder replacement active right r) :
      SubstitutedNnf binder replacement active (.And left right) (.And l r)
  | disjunction {active left right l r}
      (leftChild : SubstitutedNnf binder replacement active left l)
      (rightChild : SubstitutedNnf binder replacement active right r) :
      SubstitutedNnf binder replacement active (.Or left right) (.Or l r)
  | universal {active id body target}
      (child : SubstitutedNnf binder replacement (active && id != binder) body target) :
      SubstitutedNnf binder replacement active (.Forall id body) (.Forall id target)
  | existential {active id body target}
      (child : SubstitutedNnf binder replacement (active && id != binder) body target) :
      SubstitutedNnf binder replacement active (.Exists id body) (.Exists id target)

theorem substituted_nnf_exists (binder : U32) (replacement : fang.syntax.Term)
    (active : Bool) (formula : Nnf) : ∃ target, SubstitutedNnf binder replacement active formula target := by
  induction formula generalizing active with
  | Literal literal =>
    cases active with
    | false => exact ⟨_, .literalOff literal⟩
    | true =>
      obtain ⟨target, related⟩ := substituted_literal_exists binder replacement literal
      exact ⟨_, .literalOn related⟩
  | True => exact ⟨_, .truth active⟩
  | False => exact ⟨_, .falsity active⟩
  | And left right il ir =>
    obtain ⟨l, hl⟩ := il active
    obtain ⟨r, hr⟩ := ir active
    exact ⟨_, .conjunction hl hr⟩
  | Or left right il ir =>
    obtain ⟨l, hl⟩ := il active
    obtain ⟨r, hr⟩ := ir active
    exact ⟨_, .disjunction hl hr⟩
  | Forall id body ih =>
    obtain ⟨target, related⟩ := ih (active && id != binder)
    exact ⟨_, .universal related⟩
  | Exists id body ih =>
    obtain ⟨target, related⟩ := ih (active && id != binder)
    exact ⟨_, .existential related⟩

theorem substitute_nnf_spec (formula target : Nnf) (binder : U32) (replacement : fang.syntax.Term)
    (active : Bool) (related : SubstitutedNnf binder replacement active formula target)
    (limits : Limits) (work : Work) :
    substitute_nnf formula binder replacement active limits work
      ⦃ CopyPost (fun value => value = target) work ⦄ := by
  unfold substitute_nnf
  apply spec_bind (tick_spec work limits)
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
      cases related with
      | literalOn literalRelated =>
        simp only [ite_true]
        apply spec_mono (substitute_literal_loop_spec binder replacement limits _ _ _ literalRelated
          (alloc.vec.Vec.new _) 0#usize (by simp))
        rintro ⟨result, after⟩ ⟨hm, hp⟩
        exact ⟨by dsimp only at hm ⊢; omega, hp⟩
      | literalOff literal =>
        simp only [Bool.false_eq_true, ite_false]
        apply spec_bind (copy_literal_spec literal limits _)
        rintro ⟨result, after⟩ ⟨hm, hp⟩
        dsimp only at hm hp
        simp only [Aeneas.Std.uncurry]
        cases result with
        | Ok value =>
          subst value
          simp only [bind_ok, spec_ok, CopyPost]
          exact ⟨by omega, trivial⟩
        | Err error =>
          have post (expected : Nnf) : CopyPost (fun value => value = expected) work (.Err error, after) := by
            refine ⟨by dsimp only [Prod.snd]; omega, ?_⟩
            cases error <;> exact hp
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post _
      | truth | falsity =>
        simp only [spec_ok, CopyPost]
        exact ⟨by omega, trivial⟩
      | conjunction leftChild rightChild | disjunction leftChild rightChild =>
        apply spec_bind (substitute_nnf_spec _ _ binder replacement active leftChild limits _)
        rintro ⟨leftResult, leftWork⟩ ⟨hm, hp⟩
        dsimp only at hm hp
        simp only [Aeneas.Std.uncurry]
        cases leftResult with
        | Err error =>
          have post (expected : Nnf) : CopyPost (fun value => value = expected) work (.Err error, leftWork) := by
            refine ⟨by dsimp only [Prod.snd]; omega, ?_⟩
            cases error <;> exact hp
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post _
        | Ok leftValue =>
          subst leftValue
          simp only [bind_ok]
          apply spec_bind (substitute_nnf_spec _ _ binder replacement active rightChild limits leftWork)
          rintro ⟨rightResult, after⟩ ⟨hm2, hp2⟩
          dsimp only at hm2 hp2
          simp only [Aeneas.Std.uncurry]
          cases rightResult with
          | Err error =>
            have post (expected : Nnf) : CopyPost (fun value => value = expected) work (.Err error, after) := by
              refine ⟨by dsimp only [Prod.snd]; omega, ?_⟩
              cases error <;> exact hp2
            simpa [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post _
          | Ok rightValue =>
            subst rightValue
            simp only [bind_ok, spec_ok, CopyPost]
            exact ⟨by omega, trivial⟩
      | @universal active id body target child | @existential active id body target child =>
        dsimp only
        have flag : (if active then ok (id != binder) else ok false) =
            (ok (active && id != binder) : Result Bool) := by cases active <;> rfl
        rw [flag]
        simp only [bind_ok]
        apply spec_bind (substitute_nnf_spec body target binder replacement (active && id != binder) child limits _)
        rintro ⟨result, after⟩ ⟨hm, hp⟩
        dsimp only at hm hp
        simp only [Aeneas.Std.uncurry]
        cases result with
        | Err error =>
          have post (expected : Nnf) : CopyPost (fun value => value = expected) work (.Err error, after) := by
            refine ⟨by dsimp only [Prod.snd]; omega, ?_⟩
            cases error <;> exact hp
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post _
        | Ok value =>
          subst value
          simp only [bind_ok, spec_ok, CopyPost]
          exact ⟨by omega, trivial⟩
    next storageExceeded =>
      rw [allocated]
      simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        CopyPost, CopyResource] using (show work.statistics.operations.val ≤ operation.val by omega)
  next exceeded =>
    rw [ticked]
    simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource]
termination_by sizeOf formula

theorem substitute_nnf_total (formula : Nnf) (binder : U32) (replacement : fang.syntax.Term)
    (active : Bool) (limits : Limits) (work : Work) :
    substitute_nnf formula binder replacement active limits work
      ⦃ CopyPost (SubstitutedNnf binder replacement active formula) work ⦄ := by
  obtain ⟨target, related⟩ := substituted_nnf_exists binder replacement active formula
  apply spec_mono (substitute_nnf_spec formula target binder replacement active related limits work)
  rintro ⟨answer, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases answer with
  | Ok value => rw [hp]; exact related
  | Err error => cases error <;> exact hp

end FangSkolemCore
