/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedRenameProperties

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

theorem copy_arguments_loop_spec (arguments : Slice fang_skolem_core.fang.syntax.Term) (target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
    (stack : Bindings) (rectify : Bool) (limits : Limits) (stack_valid : StackValid stack)
    (length : target.val.length = arguments.val.length)
    (renamed : ∀ i (h : i < arguments.val.length) (ht : i < target.val.length),
      RenamedTerm stack rectify arguments.val[i] target.val[i])
    (work : Work) (copied : alloc.vec.Vec fang_skolem_core.fang.syntax.Term) (index : Usize)
    (copied_prefix : copied.val = target.val.take index.val) :
    copy_arguments_loop arguments stack rectify limits work copied index
      ⦃ CopyPost (fun value => value = target) work ⦄ := by
  unfold copy_arguments_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < arguments.val.length := by scalar_tac
    have htarget : index.val < target.val.length := by omega
    have hcopied : copied.val.length = index.val := by
      rw [copied_prefix, List.length_take]
      omega
    apply spec_bind (Slice.index_usize_spec arguments index hindex)
    intro term ht
    subst term
    apply spec_bind (copy_term_spec arguments.val[index.val] target.val[index.val] stack rectify
      (renamed index.val hindex htarget) stack_valid limits work)
    rintro ⟨answer, updated⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : CopyPost (fun value : alloc.vec.Vec fang_skolem_core.fang.syntax.Term => value = target)
          work (.Err error, updated) := by
        refine ⟨hm, ?_⟩
        cases error with
        | Resource kind => exact hp
        | Invalid kind => exact hp
        | Unsupported kind => exact hp
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok value =>
      subst value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (alloc.vec.Vec.push_spec copied target.val[index.val] (by
        have := target.property
        omega))
      intro extended extended_eq
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      intro next hn
      have hnval : next.val = index.val + 1 := by simpa using hn
      have prefix1 : extended.val = target.val.take next.val := by
        rw [extended_eq, copied_prefix, hnval]
        exact (List.take_succ_eq_append_getElem htarget).symm
      apply spec_mono (copy_arguments_loop_spec arguments target stack rectify limits stack_valid length renamed updated extended next prefix1)
      rintro ⟨result, after⟩ ⟨hm2, hp2⟩
      exact ⟨by dsimp only at hm2 ⊢; omega, hp2⟩
  next hi =>
    have hindex : target.val.length ≤ index.val := by scalar_tac
    have same : copied = target := by
      apply alloc.vec.Vec.ext
      rw [copied_prefix, List.take_of_length_le hindex]
    simp [same, CopyPost]
termination_by arguments.val.length - index.val
decreasing_by omega

theorem copy_arguments_spec (arguments : Slice fang_skolem_core.fang.syntax.Term) (target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
    (stack : Bindings) (rectify : Bool) (limits : Limits) (stack_valid : StackValid stack)
    (length : target.val.length = arguments.val.length)
    (renamed : ∀ i (h : i < arguments.val.length) (ht : i < target.val.length),
      RenamedTerm stack rectify arguments.val[i] target.val[i]) (work : Work) :
    copy_arguments arguments stack rectify limits work ⦃ CopyPost (fun value => value = target) work ⦄ :=
  copy_arguments_loop_spec arguments target stack rectify limits stack_valid length renamed
    work (alloc.vec.Vec.new _) 0#usize (by simp)

end FangSkolemEmbeddedCore
