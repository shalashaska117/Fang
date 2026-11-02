/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedCnfCopy
import ScopedRepresentation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core
variable {signature : Signature} {scope : VariableScope}
set_option maxRecDepth 2048

def clauseLists (clauses : List (alloc.vec.Vec fang.syntax.Literal)) : List (List fang.syntax.Literal) :=
  clauses.map (fun clause => clause.val)

theorem product_row_loop_spec (left : alloc.vec.Vec fang.syntax.Literal)
    (right : Slice (alloc.vec.Vec fang.syntax.Literal))
    (leftGround : (ClauseScoped signature scope) left)
    (rightGround : ∀ i (h : i < right.val.length), (ClauseScoped signature scope) right.val[i])
    (width : ∀ i (h : i < right.val.length), left.val.length + right.val[i].val.length ≤ Usize.max)
    (initial : List (List fang.syntax.Literal))
    (capacity : initial.length + right.val.length ≤ Usize.max)
    (target : alloc.vec.Vec (alloc.vec.Vec fang.syntax.Literal))
    (limits : Limits) (work : Work) (index : Usize)
    (target_prefix : clauseLists target.val = initial ++
      (right.val.take index.val).map (fun clause => left.val ++ clause.val)) :
    product_row_loop left right target limits work index
      ⦃ AppendPost (fun value => clauseLists value.val = initial ++
        right.val.map (fun clause => left.val ++ clause.val)) work ⦄ := by
  unfold product_row_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < right.val.length := by scalar_tac
    have htarget : target.val.length = initial.length + index.val := by
      have sizes := congrArg List.length target_prefix
      simp only [clauseLists, List.length_map, List.length_append, List.length_take] at sizes
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
        apply spec_bind (append_literals_spec left (alloc.vec.Vec.new _) leftGround
          (by simpa using left.property) limits _)
        rintro ⟨answer, copied, updated⟩ ⟨hm, hp⟩
        dsimp only at hm hp
        simp only [Aeneas.Std.uncurry]
        cases answer with
        | Err error =>
          have post : AppendPost (fun value => clauseLists value.val = initial ++
              right.val.map (fun clause => left.val ++ clause.val)) work (.Err error, target, updated) := by
            refine ⟨by dsimp only; omega, ?_⟩
            cases error <;> exact hp
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
        | Ok value =>
          have same : copied = left := by
            apply alloc.vec.Vec.ext
            simpa using hp
          subst copied
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          apply spec_bind (Slice.index_usize_spec right index hindex)
          intro clause hc
          subst clause
          apply spec_bind (append_literals_spec right.val[index.val] left (rightGround index.val hindex)
            (width index.val hindex) limits updated)
          rintro ⟨answer, joined, afterJoin⟩ ⟨hmJoin, joined_eq⟩
          dsimp only at hmJoin joined_eq
          simp only [Aeneas.Std.uncurry]
          cases answer with
          | Err error =>
            have post : AppendPost (fun value => clauseLists value.val = initial ++
                right.val.map (fun clause => left.val ++ clause.val)) work (.Err error, target, afterJoin) := by
              refine ⟨by dsimp only; omega, ?_⟩
              cases error <;> exact joined_eq
            simpa [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
          | Ok value =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            apply spec_bind (alloc.vec.Vec.push_spec target joined (by omega))
            intro extended extended_eq
            apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by change index.val + 1 <= Usize.max; omega))
            intro next hn
            have hnval : next.val = index.val + 1 := by simpa using hn
            have prefix1 : clauseLists extended.val = initial ++
                (right.val.take next.val).map (fun clause => left.val ++ clause.val) := by
              simp only [extended_eq, clauseLists, List.map_append, List.map_cons, List.map_nil]
              change clauseLists target.val ++ [joined.val] = _
              rw [target_prefix, joined_eq, hnval, List.take_succ_eq_append_getElem hindex]
              simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
            apply spec_mono (product_row_loop_spec left right leftGround rightGround width initial capacity
              extended limits afterJoin next prefix1)
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
    have hindex : right.val.length ≤ index.val := by scalar_tac
    simp [AppendPost, target_prefix, List.take_of_length_le hindex]
termination_by right.val.length - index.val
decreasing_by omega

theorem product_row_spec (left : alloc.vec.Vec fang.syntax.Literal)
    (right : Slice (alloc.vec.Vec fang.syntax.Literal))
    (target : alloc.vec.Vec (alloc.vec.Vec fang.syntax.Literal))
    (leftGround : (ClauseScoped signature scope) left)
    (rightGround : ∀ i (h : i < right.val.length), (ClauseScoped signature scope) right.val[i])
    (width : ∀ i (h : i < right.val.length), left.val.length + right.val[i].val.length ≤ Usize.max)
    (capacity : target.val.length + right.val.length ≤ Usize.max)
    (limits : Limits) (work : Work) :
    product_row left right target limits work
      ⦃ AppendPost (fun value => clauseLists value.val = clauseLists target.val ++
        right.val.map (fun clause => left.val ++ clause.val)) work ⦄ := by
  exact product_row_loop_spec left right leftGround rightGround width (clauseLists target.val)
    (by simpa [clauseLists] using capacity) target limits work 0#usize (by simp)

/-- The order used by the specification: left rows outside, right rows inside. -/
def rawProduct (left right : List (alloc.vec.Vec fang.syntax.Literal)) : List (List fang.syntax.Literal) :=
  left.flatMap (fun clause => right.map (fun other => clause.val ++ other.val))

theorem rawProduct_length (left right : List (alloc.vec.Vec fang.syntax.Literal)) :
    (rawProduct left right).length = left.length * right.length := by
  induction left with
  | nil => simp [rawProduct]
  | cons clause rest ih => simp_all [rawProduct, Nat.add_mul, Nat.add_comm]

theorem product_cnf_loop_spec
    (left right : alloc.vec.Vec (alloc.vec.Vec fang.syntax.Literal))
    (leftGround : ∀ i (h : i < left.val.length), (ClauseScoped signature scope) left.val[i])
    (rightGround : ∀ i (h : i < right.val.length), (ClauseScoped signature scope) right.val[i])
    (width : ∀ i (hi : i < left.val.length) j (hj : j < right.val.length),
      left.val[i].val.length + right.val[j].val.length ≤ Usize.max)
    (capacity : left.val.length * right.val.length ≤ Usize.max)
    (limits : Limits) (work : Work) (literals terms maxWidth : Usize)
    (target : alloc.vec.Vec (alloc.vec.Vec fang.syntax.Literal)) (index : Usize)
    (target_prefix : clauseLists target.val = rawProduct (left.val.take index.val) right.val) :
    product_cnf_loop left right limits work literals terms maxWidth target index
      ⦃ CopyPost (fun value => clauseLists value.clauses.val = rawProduct left.val right.val ∧
        value.literals = literals ∧ value.term_nodes = terms ∧ value.max_width = maxWidth) work ⦄ := by
  unfold product_cnf_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < left.val.length := by scalar_tac
    have htarget : target.val.length = index.val * right.val.length := by
      have sizes := congrArg List.length target_prefix
      simp only [clauseLists, List.length_map, rawProduct_length, List.length_take] at sizes
      have hi' : min index.val left.val.length = index.val := by omega
      simpa [hi'] using sizes
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec left index hindex)
    intro clause hc
    subst clause
    apply spec_bind (product_row_spec left.val[index.val] (alloc.vec.Vec.deref right) target
      (leftGround index.val hindex) (by simpa [alloc.vec.Vec.deref] using rightGround)
      (by simpa [alloc.vec.Vec.deref] using width index.val hindex)
      (by
        have stepBound := Nat.mul_le_mul_right right.val.length (show index.val + 1 ≤ left.val.length by omega)
        simpa [alloc.vec.Vec.deref, htarget, Nat.add_mul] using Nat.le_trans stepBound capacity) limits work)
    rintro ⟨answer, copied, updated⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : CopyPost (fun value : Cnf => clauseLists value.clauses.val = rawProduct left.val right.val ∧
          value.literals = literals ∧ value.term_nodes = terms ∧ value.max_width = maxWidth) work
          (.Err error, updated) := by
        refine ⟨hm, ?_⟩
        cases error <;> exact hp
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize)
        (by have := left.property; change index.val + 1 ≤ Usize.max; omega))
      intro next hn
      have hnval : next.val = index.val + 1 := by simpa using hn
      have prefix1 : clauseLists copied.val = rawProduct (left.val.take next.val) right.val := by
        rw [hnval, List.take_succ_eq_append_getElem hindex]
        simp only [rawProduct, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        simpa [alloc.vec.Vec.deref, target_prefix, rawProduct] using hp
      apply spec_mono (product_cnf_loop_spec left right leftGround rightGround width capacity limits updated
        literals terms maxWidth copied next prefix1)
      rintro ⟨result, after⟩ ⟨hm2, hp2⟩
      exact ⟨by dsimp only at hm2 ⊢; omega, hp2⟩
  next hi =>
    have hindex : left.val.length ≤ index.val := by scalar_tac
    simp [CopyPost, target_prefix, List.take_of_length_le hindex]
termination_by left.val.length - index.val
decreasing_by omega

end FangScopedFof
