/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedPublicValidation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

def CopyResource (kind : Resource) : Prop := kind = .Operations ∨ kind = .StoredNodes

def CopyPost {α : Type} (returned : α → Prop) (before : Work)
    (answer : core.result.Result α fang_skolem_core.fang_quantified_fof_core.Error × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.statistics.operations.val ∧
    match answer.1 with
    | .Ok value => returned value
    | .Err (.Invalid _) => False
    | .Err (.Resource kind) => CopyResource kind
    | .Err (.Unsupported _) => False

/-- Ordered structural copying. Rectification uses the nearest active binding;
    ordinary copying preserves every variable ID. Existence requires all renamed
    source variables to have a binding, independently of operation/storage caps. -/
inductive RenamedTerm (stack : Bindings) (rectify : Bool) : fang_skolem_core.fang.syntax.Term → fang_skolem_core.fang.syntax.Term → Prop where
  | var (id fresh : U32)
      (binding : if rectify then lookupPrefix id stack.entries.val stack.active.val = some fresh else fresh = id) :
      RenamedTerm stack rectify (.Var id) (.Var fresh)
  | fun_ (symbol : U32) (arguments target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
      (length : target.val.length = arguments.val.length)
      (children : ∀ i (h : i < arguments.val.length) (ht : i < target.val.length),
        RenamedTerm stack rectify arguments.val[i] target.val[i]) :
      RenamedTerm stack rectify (.Fun symbol arguments) (.Fun symbol target)

theorem copy_term_loop_spec (symbol : U32) (arguments target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
    (stack : Bindings) (rectify : Bool) (limits : Limits)
    (length : target.val.length = arguments.val.length)
    (child : ∀ i (h : i < arguments.val.length) (ht : i < target.val.length) work,
      copy_term arguments.val[i] stack rectify limits work
        ⦃ CopyPost (fun value => value = target.val[i]) work ⦄)
    (work : Work) (copied : alloc.vec.Vec fang_skolem_core.fang.syntax.Term) (index : Usize)
    (copied_prefix : copied.val = target.val.take index.val) :
    copy_term_loop symbol arguments stack rectify limits work copied index
      ⦃ CopyPost (fun value => value = .Fun symbol target) work ⦄ := by
  unfold copy_term_loop
  dsimp only
  split
  next hi =>
    have hindex : index.val < arguments.val.length := by scalar_tac
    have htarget : index.val < target.val.length := by omega
    have hcopied : copied.val.length = index.val := by
      rw [copied_prefix, List.length_take]
      omega
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec arguments index hindex)
    intro term ht
    subst term
    apply spec_bind (child index.val hindex htarget work)
    rintro ⟨answer, updated⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : CopyPost (fun value => value = fang_skolem_core.fang.syntax.Term.Fun symbol target) work (.Err error, updated) := by
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
      apply spec_mono (copy_term_loop_spec symbol arguments target stack rectify limits length child updated extended next prefix1)
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

theorem copy_term_spec (term target : fang_skolem_core.fang.syntax.Term) (stack : Bindings) (rectify : Bool)
    (renamed : RenamedTerm stack rectify term target) (valid : StackValid stack)
    (limits : Limits) (work : Work) :
    copy_term term stack rectify limits work ⦃ CopyPost (fun value => value = target) work ⦄ := by
  induction renamed generalizing work with
  | var id fresh binding =>
    unfold copy_term
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
        cases rectify with
        | false =>
          simp only [Bool.false_eq_true, ite_false] at binding ⊢
          subst fresh
          simp only [spec_ok, CopyPost]
          exact ⟨by omega, trivial⟩
        | true =>
          simp only [ite_true] at binding ⊢
          apply spec_bind (lookup_binding_spec id stack limits _ valid)
          rintro ⟨answer, after⟩ ⟨hm, hp⟩
          dsimp only at hm hp
          simp only [Aeneas.Std.uncurry]
          cases answer with
          | Ok found =>
            have same : found = fresh := by rw [binding] at hp; exact (Option.some.inj hp).symm
            subst found
            simp only [bind_ok, spec_ok, CopyPost]
            exact ⟨by omega, trivial⟩
          | Err error =>
            have post : CopyPost (fun value => value = fang_skolem_core.fang.syntax.Term.Var fresh) work (.Err error, after) := by
              refine ⟨by dsimp only; omega, ?_⟩
              cases error with
              | Resource kind => exact Or.inl hp
              | Invalid kind => obtain ⟨_, absent⟩ := hp; rw [binding] at absent; contradiction
              | Unsupported kind => exact hp
            simpa [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
      next exceedsAllocation =>
        rw [allocated]
        simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          CopyPost, CopyResource] using (show work.statistics.operations.val ≤ operation.val by omega)
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource]
  | fun_ symbol arguments target length children ih =>
    unfold copy_term
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
        apply spec_mono (copy_term_loop_spec symbol arguments target stack rectify limits length ih _ (alloc.vec.Vec.new _) 0#usize (by simp))
        rintro ⟨result, after⟩ ⟨hm, hp⟩
        exact ⟨by dsimp only at hm ⊢; omega, hp⟩
      next exceedsAllocation =>
        rw [allocated]
        simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          CopyPost, CopyResource] using (show work.statistics.operations.val ≤ operation.val by omega)
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource]

end FangSkolemEmbeddedCore
