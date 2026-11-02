/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Arithmetic

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

def CopyResource (kind : Resource) : Prop :=
  kind = .Operations ∨ kind = .StoredNodes ∨ kind = .TermDepth

def CopyPost {α : Type} (returned : α → Prop) (before : Work)
    (answer : core.result.Result α fang_skolem_core.Error × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.statistics.operations.val ∧
    match answer.1 with
    | .Ok value => returned value
    | .Err (.Resource kind) => CopyResource kind
    | .Err (.Core _) => False

/-- A proof abbreviation for the actual generated loop's flattened parameters. -/
abbrev copyLoop (symbol : U32) (arguments : alloc.vec.Vec fang.syntax.Term)
    (depth : Usize) (limits : Limits) (work : Work)
    (copied : alloc.vec.Vec fang.syntax.Term) (index : Usize) :=
  copy_term_loop symbol arguments depth limits.core.max_formula_depth
    limits.core.max_formula_nodes limits.core.max_term_depth limits.core.max_input_term_nodes
    limits.core.max_clauses limits.core.max_literals_per_clause limits.core.max_literals
    limits.core.max_stored_nodes limits.core.max_operations limits.core.max_binders
    limits.max_declarations limits.max_functions limits.max_skolem_symbols work copied index

theorem copy_term_loop_spec (symbol : U32) (arguments : alloc.vec.Vec fang.syntax.Term)
    (depth : Usize) (limits : Limits) (floor : Nat)
    (children : ∀ term d w, floor ≤ w.statistics.operations.val →
      copy_term term d limits w ⦃ CopyPost (fun value => value = term) w ⦄)
    (work : Work) (copied : alloc.vec.Vec fang.syntax.Term) (index : Usize)
    (copied_prefix : copied.val = arguments.val.take index.val)
    (monotone : floor ≤ work.statistics.operations.val) (bounded : depth.val ≤ 64) :
    copyLoop symbol arguments depth limits work copied index
      ⦃ CopyPost (fun value => value = .Fun symbol arguments) work ⦄ := by
  unfold copyLoop copy_term_loop
  dsimp only
  split
  next within =>
    have hi : index.val < arguments.val.length := by scalar_tac
    have length : copied.val.length = index.val := by
      rw [copied_prefix, List.length_take]
      omega
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec arguments index hi)
    intro term same
    subst term
    apply spec_bind (Usize.add_spec (x := depth) (y := 1#usize) (by scalar_tac))
    intro nextDepth depth_eq
    apply spec_bind (children arguments.val[index.val] nextDepth work monotone)
    rintro ⟨answer, updated⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : CopyPost (fun value => value = fang.syntax.Term.Fun symbol arguments)
          work (.Err error, updated) := by
        refine ⟨hm, ?_⟩
        cases error with
        | Resource kind => exact hp
        | Core kind => exact hp
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok value =>
      subst value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (alloc.vec.Vec.push_spec copied arguments.val[index.val] (by
        have := arguments.property
        omega))
      intro extended extended_eq
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      intro next next_eq
      have nextval : next.val = index.val + 1 := by simpa using next_eq
      have prefix1 : extended.val = arguments.val.take next.val := by
        rw [extended_eq, copied_prefix, nextval]
        exact (List.take_succ_eq_append_getElem hi).symm
      apply spec_mono (copy_term_loop_spec symbol arguments depth limits floor children updated
        extended next prefix1 (by omega) bounded)
      rintro ⟨result, after⟩ ⟨hm2, hp2⟩
      exact ⟨by dsimp only at hm2 ⊢; omega, hp2⟩
  next outside =>
    have hi : arguments.val.length ≤ index.val := by scalar_tac
    have same : copied = arguments := by
      apply alloc.vec.Vec.ext
      rw [copied_prefix, List.take_of_length_le hi]
    simp [same, CopyPost]
termination_by arguments.val.length - index.val
decreasing_by omega

/-- The actual copying helper terminates for every finite term and depth. Success
    preserves every symbol, variable, argument position and duplicate; failures
    have only the declared depth/operation/storage classes. -/
theorem copy_term_spec (term : fang.syntax.Term) (depth : Usize) (limits : Limits) (work : Work) :
    copy_term term depth limits work ⦃ CopyPost (fun value => value = term) work ⦄ := by
  generalize remaining : limits.core.max_operations.val - work.statistics.operations.val = fuel
  induction fuel using Nat.strong_induction_on generalizing term depth work with
  | h fuel ih =>
    unfold copy_term
    apply spec_bind (tick_spec work limits)
    intro answer ticked
    unfold TickAnswer at ticked
    split at ticked
    next fits =>
      obtain ⟨operation, rfl, operation_eq⟩ := ticked
      simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      simp only [lift, bind_ok]
      split
      next tooDeep =>
        simp only [spec_ok, CopyPost, CopyResource]
        exact ⟨by omega, Or.inr (Or.inr trivial)⟩
      next depthWithin =>
        have hd : depth.val ≤ 64 := by scalar_tac
        apply spec_bind (allocate_spec _ 1#usize limits)
        intro answer allocated
        unfold AllocationAnswer at allocated
        split at allocated
        next storageFits =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
          simp only [Aeneas.Std.uncurry, bind_ok]
          have children : ∀ t d w, operation.val ≤ w.statistics.operations.val →
              copy_term t d limits w ⦃ CopyPost (fun value => value = t) w ⦄ := by
            intro t d w hw
            exact ih (limits.core.max_operations.val - w.statistics.operations.val)
              (by omega) t d w rfl
          cases term with
          | Var id =>
            simp only [spec_ok, CopyPost]
            exact ⟨by omega, trivial⟩
          | Fun symbol arguments =>
            apply spec_mono (copy_term_loop_spec symbol arguments depth limits operation.val
              children _ (alloc.vec.Vec.new _) 0#usize (by simp) (by simp) hd)
            rintro ⟨result, after⟩ ⟨hm, hp⟩
            exact ⟨by dsimp only at hm ⊢; omega, hp⟩
        next storageExceeded =>
          rw [allocated]
          simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            CopyPost, CopyResource] using
            (show work.statistics.operations.val ≤ operation.val by omega)
    next exceeded =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource]

end FangSkolemCore
