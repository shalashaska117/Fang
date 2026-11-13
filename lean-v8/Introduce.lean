/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Actual fresh-symbol allocation, with explicit active-prefix validity. -/
import DependencyCopy

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

def IntroduceResource (kind : Resource) : Prop :=
  kind = .Operations ∨ kind = .StoredNodes ∨ kind = .Functions ∨ kind = .SkolemSymbols

def IntroducePost (before : Transformer) (binder : U32)
    (answer : core.result.Result fang.syntax.Term fang_skolem_core.Error × Transformer) : Prop :=
  answer.2.universals = before.universals ∧ answer.2.declaration = before.declaration ∧
  before.work.statistics.operations.val ≤ answer.2.work.statistics.operations.val ∧
  before.work.statistics.allocated_nodes.val ≤ answer.2.work.statistics.allocated_nodes.val ∧
  match answer.1 with
  | .Ok term => ∃ function arguments dependencies,
      term = fang.syntax.Term.Fun function arguments ∧
      function.val = before.functions.val.length ∧
      arguments.val = (before.universals.entries.val.take before.universals.active.val).map fang.syntax.Term.Var ∧
      dependencies.val = before.universals.entries.val.take before.universals.active.val ∧
      answer.2.functions.val = before.functions.val ++ [before.universals.active] ∧
      answer.2.introduced.val = before.introduced.val ++
        [{ declaration := before.declaration, binder, function, universals := dependencies }] ∧
      answer.2.work.statistics.operations.val = before.work.statistics.operations.val + 1 + before.universals.active.val ∧
      answer.2.work.statistics.allocated_nodes.val = before.work.statistics.allocated_nodes.val + 3 + 2 * before.universals.active.val
  | .Err error => answer.2.functions = before.functions ∧ answer.2.introduced = before.introduced ∧
      match error with
      | .Resource kind => IntroduceResource kind
      | .Core _ => False

theorem introduce_spec (before : Transformer) (binder : U32) (limits : Limits)
    (valid : before.universals.active.val ≤ before.universals.entries.val.length) :
    Transformer.introduce before binder limits ⦃ IntroducePost before binder ⦄ := by
  unfold Transformer.introduce
  apply spec_bind (tick_spec before.work limits)
  intro answer ticked
  unfold TickAnswer at ticked
  split at ticked
  next fits =>
    obtain ⟨operation, rfl, operation_eq⟩ := ticked
    simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
    split
    next functionsFull =>
      simp [IntroducePost, IntroduceResource, show before.work.statistics.operations.val ≤ operation.val by omega]
    next functionsFit =>
      have maximum_eq : (UScalar.cast .Usize core.num.U32.MAX).val = 4294967295 := by
        rw [U32.cast_Usize_val_eq]
        rfl
      have function_bound : before.functions.val.length < 4294967295 := by scalar_tac
      have function_capacity : before.functions.val.length < Usize.max := by scalar_tac
      split
      next skolemsFull =>
        simp [IntroducePost, IntroduceResource, show before.work.statistics.operations.val ≤ operation.val by omega]
      next skolemsFit =>
        have introduced_capacity : before.introduced.val.length < Usize.max := by scalar_tac
        let function : U32 := UScalar.cast .U32 (alloc.vec.Vec.len before.functions)
        have function_eq : function.val = before.functions.val.length := by
          dsimp [function]
          rw [UScalar.cast_val_eq]
          apply Nat.mod_eq_of_lt
          scalar_tac
        apply spec_bind (allocate_spec _ 3#usize limits)
        intro answer allocated
        unfold AllocationAnswer at allocated
        split at allocated
        next storageFits =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
          simp only [Aeneas.Std.uncurry, bind_ok]
          apply spec_bind (copy_dependencies_spec before.universals limits _ valid)
          rintro ⟨result, after⟩ ⟨hm, hs, hp⟩
          dsimp only at hm hs hp
          simp only [Aeneas.Std.uncurry]
          cases result with
          | Err error =>
            have post : IntroducePost before binder (.Err error, {before with work := after}) := by
              refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, ?_⟩
              · dsimp only; omega
              · dsimp only; scalar_tac
              · cases error with
                | Core kind => exact hp
                | Resource kind => rcases hp with same | same <;> simp [IntroduceResource, same]
            simpa [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
          | Ok pair =>
            rcases pair with ⟨arguments, dependencies⟩
            obtain ⟨args_eq, deps_eq, op_eq, storage_eq⟩ := hp
            simp only [bind_ok]
            apply spec_bind (alloc.vec.Vec.push_spec before.functions before.universals.active function_capacity)
            intro functions functions_eq
            apply spec_bind (alloc.vec.Vec.push_spec before.introduced
              { declaration := before.declaration, binder, function, universals := dependencies } introduced_capacity)
            intro introduced introduced_eq
            simp only [spec_ok, IntroducePost]
            refine ⟨trivial, trivial, ?_, ?_, function, arguments, dependencies, rfl, function_eq,
              args_eq, deps_eq, functions_eq, introduced_eq, ?_, ?_⟩
            · omega
            · scalar_tac
            · scalar_tac
            · scalar_tac
        next storageExceeded =>
          rw [allocated]
          have post : IntroducePost before binder (.Err (.Resource .StoredNodes),
              { before with work := { statistics := { before.work.statistics with operations := operation } } }) := by
            exact ⟨rfl, rfl, by dsimp only; omega, Nat.le_refl _, rfl, rfl, Or.inr (Or.inl rfl)⟩
          simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
  next exceeded =>
    rw [ticked]
    simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, IntroducePost, IntroduceResource]

end FangSkolemCore
