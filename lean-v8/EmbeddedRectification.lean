/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Direct refinement of the unchanged Rust whole-formula rectifier. -/
import EmbeddedRectifyState

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

def StackResolver (stack : Bindings) (id : U32) : Option U32 :=
  lookupPrefix id stack.entries.val stack.active.val

def RectifyResource (kind : Resource) : Prop := CopyResource kind ∨ kind = .Binders

def RectifyPost (stack : Bindings) (next : U32) (source : Formula) (work : Work)
    (answer : core.result.Result Formula fang_skolem_core.fang_quantified_fof_core.Error × Bindings × U32 × Work) : Prop :=
  StackValid answer.2.1 ∧ StackFrame stack answer.2.1 ∧
  next.val ≤ answer.2.2.1.val ∧ work.statistics.operations.val ≤ answer.2.2.2.statistics.operations.val ∧
    match answer.1 with
    | .Ok target => RectifiedFormula (StackResolver stack) next.val source target answer.2.2.1.val
    | .Err (.Invalid _) => False
    | .Err (.Resource kind) => RectifyResource kind
    | .Err (.Unsupported _) => False

theorem rectify_formula_spec (formula : Formula) (signature : Signature) (stack : Bindings)
    (next : U32) (limits : Limits) (work : Work) (stack_valid : StackValid stack)
    (stack_count : stack.active.val ≤ next.val)
    (source_valid : StackFormulaValid signature .Ground stack formula) :
    rectify_formula formula stack next limits work ⦃ RectifyPost stack next formula work ⦄ := by
  generalize hn : limits.max_operations.val - work.statistics.operations.val = n
  induction n using Nat.strong_induction_on generalizing formula stack next work with
  | h n ih =>
    unfold rectify_formula
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
        let updated : Work := {statistics := {work.statistics with operations := operation, allocated_nodes := nodes}}
        have hc : ∀ f s k w, operation.val ≤ w.statistics.operations.val → StackValid s →
            s.active.val ≤ k.val → StackFormulaValid signature .Ground s f →
            rectify_formula f s k limits w ⦃ RectifyPost s k f w ⦄ := by
          intro f s k w hw hs hk hf
          exact ih (limits.max_operations.val - w.statistics.operations.val) (by omega) f s k w hs hk hf rfl
        cases formula with
        | Atom predicate arguments =>
          have arguments_valid : ∀ i (h : i < arguments.val.length),
              TermValid signature .Ground stack arguments.val[i] := by
            intro i hi
            exact (termValid_iff_scoped signature .Ground stack _).mpr (source_valid.2 i hi)
          obtain ⟨target, length, renamed⟩ := arguments_renaming_exists arguments stack signature arguments_valid
          apply spec_bind (copy_arguments_spec (alloc.vec.Vec.deref arguments) target stack true limits stack_valid
            (by simpa [alloc.vec.Vec.deref] using length) (by simpa [alloc.vec.Vec.deref] using renamed) updated)
          rintro ⟨answer, after⟩ ⟨hm, hp⟩
          dsimp only at hm hp
          simp only [Aeneas.Std.uncurry]
          cases answer with
          | Err error =>
            have post : RectifyPost stack next (.Atom predicate arguments) work (.Err error, stack, next, after) := by
              refine ⟨stack_valid, stackFrame_refl stack, Nat.le_refl _, ?_, ?_⟩
              · dsimp [updated] at hm; dsimp only; omega
              · cases error with
                | Resource kind => exact Or.inl hp
                | Invalid kind => exact hp
                | Unsupported kind => exact hp
            simpa [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
          | Ok value =>
            subst value
            simp only [bind_ok, spec_ok, RectifyPost]
            refine ⟨stack_valid, stackFrame_refl stack, Nat.le_refl _, ?_, ?_⟩
            · dsimp [updated] at hm; omega
            · exact .atom next.val predicate arguments target length
                (fun i hi ht => (renamedTerm_iff_renaming stack _ _).mp (renamed i hi ht))
        | True =>
          simp only [spec_ok, RectifyPost]
          exact ⟨stack_valid, stackFrame_refl stack, Nat.le_refl _, by omega, .truth _⟩
        | False =>
          simp only [spec_ok, RectifyPost]
          exact ⟨stack_valid, stackFrame_refl stack, Nat.le_refl _, by omega, .falsity _⟩
        | Not body =>
          apply spec_bind (hc body stack next updated (by simp [updated]) stack_valid stack_count source_valid)
          rintro ⟨answer, afterstack, afterNext, after⟩ ⟨validstack, frame, counter, hm, hp⟩
          dsimp only at counter hm hp
          have monotone : work.statistics.operations.val ≤ after.statistics.operations.val := by
            dsimp [updated] at hm; omega
          simp only [Aeneas.Std.uncurry]
          cases answer with
          | Err error =>
            have post : RectifyPost stack next (.Not body) work (.Err error, afterstack, afterNext, after) := by
              refine ⟨validstack, frame, counter, monotone, ?_⟩
              cases error <;> exact hp
            simpa [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
          | Ok value =>
            simp only [bind_ok, spec_ok, RectifyPost]
            exact ⟨validstack, frame, counter, monotone, .negation hp⟩
        | And left right | Or left right | Implies left right =>
          apply spec_bind (hc left stack next updated (by simp [updated]) stack_valid stack_count source_valid.1)
          rintro ⟨answer, middle, middleNext, afterleft⟩ ⟨middle_valid, middle_frame, middle_count, hm, hp⟩
          dsimp only at middle_count hm hp
          have hm' : operation.val ≤ afterleft.statistics.operations.val := by simpa [updated] using hm
          simp only [Aeneas.Std.uncurry]
          cases answer with
          | Err error =>
            simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              RectifyPost, middle_valid, middle_frame, middle_count,
              show work.statistics.operations.val ≤ afterleft.statistics.operations.val by omega]
            cases error <;> exact hp
          | Ok l =>
            simp only [bind_ok]
            have frame_depth : middle.active.val = stack.active.val := middle_frame.1
            have middle_bound : middle.active.val ≤ middleNext.val := by omega
            have right_valid := (stackFrame_formula middle_frame signature .Ground right).mpr source_valid.2
            apply spec_bind (hc right middle middleNext afterleft hm' middle_valid middle_bound right_valid)
            rintro ⟨result, afterstack, afterNext, after⟩ ⟨validstack, frame, counter, hm2, hp2⟩
            dsimp only at counter hm2 hp2
            have final_frame := stackFrame_trans middle_frame frame
            have final_counter : next.val ≤ afterNext.val := by omega
            have monotone : work.statistics.operations.val ≤ after.statistics.operations.val := by omega
            simp only [Aeneas.Std.uncurry]
            cases result with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                RectifyPost, validstack, final_frame, final_counter, monotone]
              cases error <;> exact hp2
            | Ok r =>
              have right_original := rectifiedFormula_congr (stackFrame_lookup middle_frame) hp2
              simp only [bind_ok, spec_ok, RectifyPost]
              refine ⟨validstack, final_frame, final_counter, monotone, ?_⟩
              first | exact .conjunction hp right_original | exact .disjunction hp right_original | exact .implication hp right_original
        | Forall id body | Exists id body =>
          have checked := U32.checked_add_bv_spec next 1#u32
          cases computation : U32.checked_add next 1#u32 with
          | none =>
            simp only [computation] at checked
            simp [lift, core.option.Option.ok_or,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              RectifyPost, RectifyResource, stack_valid, stackFrame_refl,
              show work.statistics.operations.val ≤ operation.val by omega]
          | some successor =>
            simp only [computation] at checked
            have successor_eq : successor.val = next.val + 1 := by simpa using checked.2.1
            simp only [lift, bind_ok, core.option.Option.ok_or]
            apply spec_bind (allocate_spec updated 1#usize limits)
            intro answer allocated_stack
            unfold AllocationAnswer at allocated_stack
            split at allocated_stack
            next stackFits =>
              obtain ⟨stack_nodes, rfl, stack_nodes_eq⟩ := allocated_stack
              simp only [Aeneas.Std.uncurry, bind_ok]
              apply spec_bind (bindings_push_spec stack {original := id, fresh := next} stack_valid (by scalar_tac))
              intro pushed ⟨pushed_valid, pushed_depth, pushed_entries⟩
              have body_valid := (pushed_formula_any stack pushed id next .Ground signature body stack_valid pushed_depth pushed_entries).mpr source_valid
              let under : Work := {statistics := {updated.statistics with allocated_nodes := stack_nodes}}
              apply spec_bind (hc body pushed successor under (by simp [under, updated]) pushed_valid (by scalar_tac) body_valid)
              rintro ⟨result, inner, afterNext, after⟩ ⟨inner_valid, inner_frame, counter, hm, hp⟩
              dsimp only at counter hm hp
              apply spec_bind (bindings_pop_spec inner inner_valid)
              intro popped ⟨popped_valid, popped_depth, popped_entries⟩
              have final_frame := popped_frame stack pushed inner popped {original := id, fresh := next}
                stack_valid pushed_depth pushed_entries inner_frame popped_depth popped_entries
              have final_counter : next.val ≤ afterNext.val := by omega
              have monotone : work.statistics.operations.val ≤ after.statistics.operations.val := by
                dsimp [under, updated] at hm; omega
              cases result with
              | Err error =>
                simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  RectifyPost, popped_valid, final_frame, final_counter, monotone]
                cases error <;> exact hp
              | Ok value =>
                have body_relation : RectifiedFormula
                    (shadowResolver (StackResolver stack) id next) (next.val + 1) body value afterNext.val := by
                  change RectifiedFormula (StackResolver pushed) successor.val body value afterNext.val at hp
                  have resolver_eq : StackResolver pushed = shadowResolver (StackResolver stack) id next :=
                    pushed_resolver stack pushed id next stack_valid pushed_depth pushed_entries
                  rw [resolver_eq, successor_eq] at hp
                  exact hp
                simp only [bind_ok, spec_ok, RectifyPost]
                refine ⟨popped_valid, final_frame, final_counter, monotone, ?_⟩
                first | exact .universal rfl body_relation | exact .existential rfl body_relation
            next stackExceeded =>
              rw [allocated_stack]
              simp [Aeneas.Std.uncurry,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                RectifyPost, RectifyResource, CopyResource, stack_valid, stackFrame_refl,
                updated, show work.statistics.operations.val ≤ operation.val by omega, show next.val ≤ successor.val by omega]
      next exceedsAllocation =>
        rw [allocated]
        simp [Aeneas.Std.uncurry,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          RectifyPost, RectifyResource, CopyResource, stack_valid, stackFrame_refl,
          show work.statistics.operations.val ≤ operation.val by omega]
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        RectifyPost, RectifyResource, CopyResource, stack_valid, stackFrame_refl]

end FangSkolemEmbeddedCore
