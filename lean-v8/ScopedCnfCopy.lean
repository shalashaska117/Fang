/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedCopy

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core
variable {signature : Signature} {scope : VariableScope}
set_option maxRecDepth 2048

def LiteralScoped (signature : Signature) (scope : VariableScope) (literal : fang.syntax.Literal) : Prop :=
  ∀ i (h : i < literal.arguments.val.length), (TermValid signature scope) literal.arguments.val[i]

def ClauseScoped (signature : Signature) (scope : VariableScope) (clause : alloc.vec.Vec fang.syntax.Literal) : Prop :=
  ∀ i (h : i < clause.val.length), (LiteralScoped signature scope) clause.val[i]

/-- The generated helper returns an exact copy; resource errors may retain private work. -/
theorem copy_literal_spec (literal : fang.syntax.Literal) (ground : (LiteralScoped signature scope) literal)
    (limits : Limits) (work : Work) :
    copy_literal literal limits work ⦃ CopyPost (fun value => value = literal) work ⦄ := by
  unfold copy_literal
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
    next fitsAllocation =>
      obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
      simp only [Aeneas.Std.uncurry, bind_ok]
      apply spec_bind (copy_arguments_spec (alloc.vec.Vec.deref literal.arguments) limits
        (by simpa [alloc.vec.Vec.deref, LiteralScoped] using ground) _)
      rintro ⟨result, after⟩ ⟨hm, hp⟩
      dsimp only at hm hp
      simp only [Aeneas.Std.uncurry]
      cases result with
      | Ok value =>
        have same : value = literal.arguments := by
          apply alloc.vec.Vec.ext
          simpa [alloc.vec.Vec.deref] using hp
        subst value
        simpa [core.result.Result.Insts.CoreOpsTry.branch, CopyPost] using
          (show work.statistics.operations.val ≤ after.statistics.operations.val by omega)
      | Err error =>
        have post : CopyPost (fun value => value = literal) work (.Err error, after) := by
          refine ⟨by dsimp only; omega, ?_⟩
          cases error <;> exact hp
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost] using post
    next exceedsAllocation =>
      rw [allocated]
      simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        CopyPost, CopyResource] using (show work.statistics.operations.val ≤ operation.val by omega)
  next exceedsOperations =>
    rw [ticked]
    simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource]

/-- Private append helpers can return a partial buffer on resource exhaustion. -/
def AppendPost {α : Type} (returned : alloc.vec.Vec α → Prop) (before : Work)
    (answer : core.result.Result Unit fang_fof_core.Error × alloc.vec.Vec α × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.2.statistics.operations.val ∧
    match answer.1 with
    | .Ok _ => returned answer.2.1
    | .Err (.Invalid _) => False
    | .Err (.Resource kind) => CopyResource kind

theorem append_literals_loop_spec (source : alloc.vec.Vec fang.syntax.Literal)
    (ground : (ClauseScoped signature scope) source) (initial : List fang.syntax.Literal)
    (capacity : initial.length + source.val.length ≤ Usize.max)
    (target : alloc.vec.Vec fang.syntax.Literal) (limits : Limits) (work : Work) (index : Usize)
    (target_prefix : target.val = initial ++ source.val.take index.val) :
    append_literals_loop source target limits work index
      ⦃ AppendPost (fun value => value.val = initial ++ source.val) work ⦄ := by
  unfold append_literals_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < source.val.length := by scalar_tac
    have htarget : target.val.length = initial.length + index.val := by
      rw [target_prefix, List.length_append, List.length_take]
      omega
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec source index hindex)
    intro literal hl
    subst literal
    apply spec_bind (copy_literal_spec source.val[index.val] (ground index.val hindex) limits work)
    rintro ⟨answer, updated⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : AppendPost (fun value => value.val = initial ++ source.val) work
          (.Err error, target, updated) := by
        refine ⟨hm, ?_⟩
        cases error <;> exact hp
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok value =>
      subst value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (alloc.vec.Vec.push_spec target source.val[index.val] (by omega))
      intro extended extended_eq
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by change index.val + 1 <= Usize.max; omega))
      intro next hn
      have hnval : next.val = index.val + 1 := by simpa using hn
      have prefix1 : extended.val = initial ++ source.val.take next.val := by
        rw [extended_eq, target_prefix, hnval, List.take_succ_eq_append_getElem hindex,
          List.append_assoc]
      apply spec_mono (append_literals_loop_spec source ground initial capacity extended limits updated next prefix1)
      rintro ⟨result, buffer, after⟩ ⟨hm2, hp2⟩
      exact ⟨by dsimp only at hm2 ⊢; omega, hp2⟩
  next hi =>
    have hindex : source.val.length ≤ index.val := by scalar_tac
    simp [AppendPost, target_prefix, List.take_of_length_le hindex]
termination_by source.val.length - index.val
decreasing_by omega

theorem append_literals_spec (source target : alloc.vec.Vec fang.syntax.Literal)
    (ground : (ClauseScoped signature scope) source) (capacity : target.val.length + source.val.length ≤ Usize.max)
    (limits : Limits) (work : Work) :
    append_literals source target limits work
      ⦃ AppendPost (fun value => value.val = target.val ++ source.val) work ⦄ := by
  exact append_literals_loop_spec source ground target.val capacity target limits work 0#usize (by simp)

theorem append_clauses_loop_spec (source : Slice (alloc.vec.Vec fang.syntax.Literal))
    (ground : ∀ i (h : i < source.val.length), (ClauseScoped signature scope) source.val[i])
    (initial : List (alloc.vec.Vec fang.syntax.Literal))
    (capacity : initial.length + source.val.length ≤ Usize.max)
    (target : alloc.vec.Vec (alloc.vec.Vec fang.syntax.Literal))
    (limits : Limits) (work : Work) (index : Usize)
    (target_prefix : target.val = initial ++ source.val.take index.val) :
    append_clauses_loop source target limits work index
      ⦃ AppendPost (fun value => value.val = initial ++ source.val) work ⦄ := by
  unfold append_clauses_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < source.val.length := by scalar_tac
    have htarget : target.val.length = initial.length + index.val := by
      rw [target_prefix, List.length_append, List.length_take]
      omega
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
      next fitsAllocation =>
        obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
        simp only [Aeneas.Std.uncurry, bind_ok]
        apply spec_bind (Slice.index_usize_spec source index hindex)
        intro clause hc
        subst clause
        apply spec_bind (append_literals_spec source.val[index.val] (alloc.vec.Vec.new _) (ground index.val hindex)
          (by simpa using source.val[index.val].property) limits _)
        rintro ⟨answer, copied, updated⟩ ⟨hm, hp⟩
        dsimp only at hm hp
        simp only [Aeneas.Std.uncurry]
        cases answer with
        | Err error =>
          have post : AppendPost (fun value => value.val = initial ++ source.val) work
              (.Err error, target, updated) := by
            refine ⟨by dsimp only; omega, ?_⟩
            cases error <;> exact hp
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
        | Ok value =>
          have same : copied = source.val[index.val] := by
            apply alloc.vec.Vec.ext
            simpa using hp
          subst copied
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          apply spec_bind (alloc.vec.Vec.push_spec target source.val[index.val] (by omega))
          intro extended extended_eq
          apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by change index.val + 1 <= Usize.max; omega))
          intro next hn
          have hnval : next.val = index.val + 1 := by simpa using hn
          have prefix1 : extended.val = initial ++ source.val.take next.val := by
            rw [extended_eq, target_prefix, hnval, List.take_succ_eq_append_getElem hindex,
              List.append_assoc]
          apply spec_mono (append_clauses_loop_spec source ground initial capacity extended limits updated next prefix1)
          rintro ⟨result, buffer, after⟩ ⟨hm2, hp2⟩
          exact ⟨by dsimp only at hm2 ⊢; omega, hp2⟩
      next exceedsAllocation =>
        rw [allocated]
        simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          AppendPost, CopyResource] using (show work.statistics.operations.val ≤ operation.val by omega)
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, AppendPost, CopyResource]
  next hi =>
    have hindex : source.val.length ≤ index.val := by scalar_tac
    simp [AppendPost, target_prefix, List.take_of_length_le hindex]
termination_by source.val.length - index.val
decreasing_by omega

theorem append_clauses_spec (source : Slice (alloc.vec.Vec fang.syntax.Literal))
    (target : alloc.vec.Vec (alloc.vec.Vec fang.syntax.Literal))
    (ground : ∀ i (h : i < source.val.length), (ClauseScoped signature scope) source.val[i])
    (capacity : target.val.length + source.val.length ≤ Usize.max)
    (limits : Limits) (work : Work) :
    append_clauses source target limits work
      ⦃ AppendPost (fun value => value.val = target.val ++ source.val) work ⦄ := by
  exact append_clauses_loop_spec source ground target.val capacity target limits work 0#usize (by simp)

end FangScopedFof
