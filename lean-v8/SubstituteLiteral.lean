/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import CopyLiteral

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

def SubstitutedLiteral (binder : U32) (replacement : fang.syntax.Term)
    (source target : fang.syntax.Literal) : Prop :=
  target.positive = source.positive ∧ target.predicate = source.predicate ∧
    target.arguments.val.length = source.arguments.val.length ∧
    ∀ i (hs : i < source.arguments.val.length) (ht : i < target.arguments.val.length),
      SubstitutedTerm binder replacement source.arguments.val[i] target.arguments.val[i]

theorem substituted_literal_exists (binder : U32) (replacement : fang.syntax.Term)
    (literal : fang.syntax.Literal) : ∃ target, SubstitutedLiteral binder replacement literal target := by
  obtain ⟨target, related⟩ := substituted_exists binder replacement (.Fun 0#u32 literal.arguments)
  cases related with
  | fun_ symbol arguments target length children =>
    exact ⟨{ literal with arguments := target }, rfl, rfl, length, children⟩

theorem substitute_literal_loop_spec (binder : U32) (replacement : fang.syntax.Term)
    (limits : Limits) (work : Work) (literal target : fang.syntax.Literal)
    (related : SubstitutedLiteral binder replacement literal target)
    (arguments : alloc.vec.Vec fang.syntax.Term) (index : Usize)
    (copied_prefix : arguments.val = target.arguments.val.take index.val) :
    substitute_nnf_loop binder replacement limits work literal arguments index
      ⦃ CopyPost (fun value => value = .Literal target) work ⦄ := by
  obtain ⟨positive, predicate, length, children⟩ := related
  unfold substitute_nnf_loop
  dsimp only
  split
  next within =>
    have hi : index.val < literal.arguments.val.length := by scalar_tac
    have ht : index.val < target.arguments.val.length := by omega
    have hcopied : arguments.val.length = index.val := by
      rw [copied_prefix, List.length_take]
      omega
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec literal.arguments index hi)
    intro term same
    subst term
    apply spec_bind (substitute_term_spec literal.arguments.val[index.val]
      target.arguments.val[index.val] binder replacement (children index.val hi ht) 1#usize limits work)
    rintro ⟨answer, updated⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : CopyPost (fun value => value = fang_quantified_fof_core.Nnf.Literal target)
          work (.Err error, updated) := by
        refine ⟨hm, ?_⟩
        cases error <;> exact hp
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok value =>
      subst value
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (alloc.vec.Vec.push_spec arguments target.arguments.val[index.val] (by
        have := target.arguments.property
        omega))
      intro extended extended_eq
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      intro next next_eq
      have nextval : next.val = index.val + 1 := by simpa using next_eq
      have prefix1 : extended.val = target.arguments.val.take next.val := by
        rw [extended_eq, copied_prefix, nextval]
        exact (List.take_succ_eq_append_getElem ht).symm
      apply spec_mono (substitute_literal_loop_spec binder replacement limits updated literal target
        ⟨positive, predicate, length, children⟩ extended next prefix1)
      rintro ⟨result, after⟩ ⟨hm2, hp2⟩
      exact ⟨by dsimp only at hm2 ⊢; omega, hp2⟩
  next outside =>
    have hi : target.arguments.val.length ≤ index.val := by scalar_tac
    have same : arguments = target.arguments := by
      apply alloc.vec.Vec.ext
      rw [copied_prefix, List.take_of_length_le hi]
    have result_same : { literal with arguments } = target := by
      cases literal; cases target
      simp_all
    simp [result_same, CopyPost]
termination_by literal.arguments.val.length - index.val
decreasing_by omega

end FangSkolemCore
