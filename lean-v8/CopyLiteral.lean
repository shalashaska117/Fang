/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import SubstituteSemantics

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

theorem copy_literal_loop_spec (literal : fang.syntax.Literal) (limits : Limits) (work : Work)
    (arguments : alloc.vec.Vec fang.syntax.Term) (index : Usize)
    (copied_prefix : arguments.val = literal.arguments.val.take index.val) :
    copy_literal_loop literal limits work arguments index
      ⦃ CopyPost (fun value => value = literal) work ⦄ := by
  unfold copy_literal_loop
  dsimp only
  split
  next within =>
    have hi : index.val < literal.arguments.val.length := by scalar_tac
    have hcopied : arguments.val.length = index.val := by
      rw [copied_prefix, List.length_take]
      omega
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec literal.arguments index hi)
    intro term same
    subst term
    apply spec_bind (copy_term_spec literal.arguments.val[index.val] 1#usize limits work)
    rintro ⟨answer, updated⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : CopyPost (fun value => value = literal) work (.Err error, updated) := by
        refine ⟨hm, ?_⟩
        cases error <;> exact hp
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok value =>
      subst value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (alloc.vec.Vec.push_spec arguments literal.arguments.val[index.val] (by
        have := literal.arguments.property
        omega))
      intro extended extended_eq
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      intro next next_eq
      have nextval : next.val = index.val + 1 := by simpa using next_eq
      have prefix1 : extended.val = literal.arguments.val.take next.val := by
        rw [extended_eq, copied_prefix, nextval]
        exact (List.take_succ_eq_append_getElem hi).symm
      apply spec_mono (copy_literal_loop_spec literal limits updated extended next prefix1)
      rintro ⟨result, after⟩ ⟨hm2, hp2⟩
      exact ⟨by dsimp only at hm2 ⊢; omega, hp2⟩
  next outside =>
    have hi : literal.arguments.val.length ≤ index.val := by scalar_tac
    have same : arguments = literal.arguments := by
      apply alloc.vec.Vec.ext
      rw [copied_prefix, List.take_of_length_le hi]
    simp [same, CopyPost]
termination_by literal.arguments.val.length - index.val
decreasing_by omega

theorem copy_literal_spec (literal : fang.syntax.Literal) (limits : Limits) (work : Work) :
    copy_literal literal limits work ⦃ CopyPost (fun value => value = literal) work ⦄ := by
  unfold copy_literal
  exact copy_literal_loop_spec literal limits work _ _ (by simp)

end FangSkolemCore
