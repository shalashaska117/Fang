/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact active-prefix copying over the actual generated Rust helper. -/
import SubstituteCapture

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

def DependencyPost (universals : Universals) (index : Usize) (before : Work)
    (answer : core.result.Result (alloc.vec.Vec fang.syntax.Term × alloc.vec.Vec U32) fang_skolem_core.Error × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.statistics.operations.val ∧
  before.statistics.allocated_nodes.val ≤ answer.2.statistics.allocated_nodes.val ∧
  match answer.1 with
  | .Ok (arguments, dependencies) =>
      arguments.val = (universals.entries.val.take universals.active.val).map fang.syntax.Term.Var ∧
      dependencies.val = universals.entries.val.take universals.active.val ∧
      answer.2.statistics.operations.val = before.statistics.operations.val + (universals.active.val - index.val) ∧
      answer.2.statistics.allocated_nodes.val = before.statistics.allocated_nodes.val + 2 * (universals.active.val - index.val)
  | .Err (.Resource kind) => kind = .Operations ∨ kind = .StoredNodes
  | .Err (.Core _) => False

theorem copy_dependencies_loop_spec (universals : Universals) (limits : Limits) (work : Work)
    (arguments : alloc.vec.Vec fang.syntax.Term) (dependencies : alloc.vec.Vec U32) (index : Usize)
    (valid : universals.active.val ≤ universals.entries.val.length)
    (inside : index.val ≤ universals.active.val)
    (argumentPrefix : arguments.val = (universals.entries.val.take index.val).map fang.syntax.Term.Var)
    (dependencyPrefix : dependencies.val = universals.entries.val.take index.val) :
    copy_dependencies_loop universals limits work arguments dependencies index
      ⦃ DependencyPost universals index work ⦄ := by
  unfold copy_dependencies_loop
  split
  next more =>
    have hi : index.val < universals.entries.val.length := by scalar_tac
    have ha : arguments.val.length = index.val := by
      rw [argumentPrefix, List.length_map, List.length_take]
      omega
    have hd : dependencies.val.length = index.val := by
      rw [dependencyPrefix, List.length_take]
      omega
    apply spec_bind (tick_spec work limits)
    intro answer ticked
    unfold TickAnswer at ticked
    split at ticked
    next fits =>
      obtain ⟨operation, rfl, operation_eq⟩ := ticked
      simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (allocate_spec _ 2#usize limits)
      intro answer allocated
      unfold AllocationAnswer at allocated
      split at allocated
      next storageFits =>
        obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
        simp only [Aeneas.Std.uncurry, bind_ok]
        rw [alloc.vec.Vec.index_slice_index]
        apply spec_bind (alloc.vec.Vec.index_usize_spec universals.entries index hi)
        intro id same
        subst id
        apply spec_bind (alloc.vec.Vec.push_spec arguments (.Var universals.entries.val[index.val]) (by
          have := universals.entries.property
          omega))
        intro nextArguments arguments_eq
        apply spec_bind (alloc.vec.Vec.push_spec dependencies universals.entries.val[index.val] (by
          have := universals.entries.property
          omega))
        intro nextDependencies dependencies_eq
        apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
        intro next next_eq
        have nextval : next.val = index.val + 1 := by simpa using next_eq
        have argumentNext : nextArguments.val =
            (universals.entries.val.take next.val).map fang.syntax.Term.Var := by
          rw [arguments_eq, argumentPrefix, nextval, List.take_succ_eq_append_getElem hi, List.map_append]
          rfl
        have dependencyNext : nextDependencies.val = universals.entries.val.take next.val := by
          rw [dependencies_eq, dependencyPrefix, nextval]
          exact (List.take_succ_eq_append_getElem hi).symm
        apply spec_mono (copy_dependencies_loop_spec universals limits _ nextArguments nextDependencies next
          valid (by scalar_tac) argumentNext dependencyNext)
        rintro ⟨result, after⟩ ⟨hm, hs, post⟩
        dsimp only at hm hs post
        refine ⟨by dsimp only; omega, by dsimp only; scalar_tac, ?_⟩
        cases result with
        | Err error => cases error <;> exact post
        | Ok pair =>
          rcases pair with ⟨args, deps⟩
          obtain ⟨ha, hd, hop, hnodes⟩ := post
          exact ⟨ha, hd, by dsimp only; scalar_tac, by dsimp only; scalar_tac⟩
      next storageExceeded =>
        rw [allocated]
        have post : DependencyPost universals index work (.Err (.Resource .StoredNodes),
            { statistics := { work.statistics with operations := operation } }) := by
          exact ⟨by dsimp only; omega, Nat.le_refl _, Or.inr rfl⟩
        simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    next exceeded =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, DependencyPost]
  next done =>
    have last : index.val = universals.active.val := by scalar_tac
    simp [DependencyPost, argumentPrefix, dependencyPrefix, last]
termination_by universals.active.val - index.val
decreasing_by scalar_tac

theorem copy_dependencies_spec (universals : Universals) (limits : Limits) (work : Work)
    (valid : universals.active.val ≤ universals.entries.val.length) :
    copy_dependencies universals limits work ⦃ DependencyPost universals 0#usize work ⦄ := by
  unfold copy_dependencies
  exact copy_dependencies_loop_spec universals limits work _ _ _ valid (by simp) (by simp) (by simp)

end FangSkolemCore
