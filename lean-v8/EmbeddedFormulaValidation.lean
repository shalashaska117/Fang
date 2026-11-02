/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedFormulaScope

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

def FormulaResource (kind : Resource) : Prop :=
  TermResource kind ∨ kind = .FormulaDepth ∨ kind = .FormulaNodes ∨ kind = .Binders

def FormulaPost (stack : Bindings) (valid : Prop) (work : Work)
    (answer : core.result.Result Unit fang_skolem_core.fang_quantified_fof_core.Error × Bindings × Work) : Prop :=
  StackValid answer.2.1 ∧ StackFrame stack answer.2.1 ∧
    ValidationPost valid FormulaResource work (answer.1, answer.2.2)

theorem validate_formula_loop_spec (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
    (signature : Signature) (scope : VariableScope) (stack : Bindings) (limits : Limits)
    (work : Work) (index : Usize) (stack_valid : StackValid stack) :
    validate_formula_loop arguments signature.functions signature.predicates scope stack
      limits.max_formula_depth limits.max_formula_nodes limits.max_term_depth
      limits.max_input_term_nodes limits.max_clauses limits.max_literals_per_clause
      limits.max_literals limits.max_stored_nodes limits.max_operations limits.max_binders work index
      ⦃ ValidationPost (TermsFrom signature scope stack arguments index.val) TermResource work ⦄ := by
  unfold validate_formula_loop
  dsimp only
  split
  next hindex =>
    have hlt : index.val < arguments.val.length := by scalar_tac
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec arguments index hlt)
    intro term ht
    subst term
    apply spec_bind (validate_term_spec arguments.val[index.val] 1#usize signature scope stack limits work stack_valid)
    rintro ⟨answer, updated⟩ ⟨hm, hc⟩
    dsimp only at hm hc
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      have post : ValidationPost (TermsFrom signature scope stack arguments index.val) TermResource work
          (.Err error, updated) := by
        refine ⟨hm, ?_⟩
        cases error with
        | Unsupported kind => exact hc
        | Resource kind => exact hc
        | Invalid kind => exact fun valid => hc (valid index.val (by omega) hlt)
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    | Ok output =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      apply spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
      intro next hn
      have hnval : next.val = index.val + 1 := by simpa using hn
      apply spec_mono (validate_formula_loop_spec arguments signature scope stack limits updated next stack_valid)
      rintro ⟨result, after⟩ ⟨hm2, hc2⟩
      dsimp only at hm2 hc2
      refine ⟨by dsimp only; omega, ?_⟩
      cases result with
      | Ok value =>
        intro i hi hi'
        by_cases same : i = index.val
        · subst i; exact hc
        · exact hc2 i (by omega) hi'
      | Err error =>
        cases error with
        | Unsupported kind => exact hc2
        | Resource kind => exact hc2
        | Invalid kind => exact fun valid => hc2 (fun i hi hi' => valid i (by omega) hi')
  next hindex =>
    simp only [spec_ok, ValidationPost]
    refine ⟨Nat.le_refl _, ?_⟩
    intro i hi hi'
    have : arguments.val.length ≤ index.val := by scalar_tac
    omega
termination_by arguments.val.length - index.val
decreasing_by omega

theorem validate_formula_spec (formula : Formula) (depth : Usize) (signature : Signature)
    (scope : VariableScope) (stack : Bindings) (limits : Limits) (work : Work)
    (stack_valid : StackValid stack) (stack_depth : stack.active.val ≤ depth.val) :
    validate_formula formula depth signature scope stack limits work
      ⦃ FormulaPost stack (StackFormulaValid signature scope stack formula) work ⦄ := by
  generalize hn : limits.max_operations.val - work.statistics.operations.val = n
  induction n using Nat.strong_induction_on generalizing formula depth stack work with
  | h n ih =>
    unfold validate_formula
    apply spec_bind (tick_spec work limits)
    intro answer checked
    unfold TickAnswer at checked
    split at checked
    next fits =>
      obtain ⟨operation, rfl, operation_eq⟩ := checked
      simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
      split
      next depthExceeded =>
        simp only [spec_ok, FormulaPost, ValidationPost, FormulaResource]
        exact ⟨stack_valid, stackFrame_refl stack, by omega, Or.inr (Or.inl trivial)⟩
      next depthWithin =>
        have hd : depth.val ≤ 64 := by scalar_tac
        apply spec_bind (bounded_add_spec work.statistics.input_formula_nodes 1#usize
          limits.max_formula_nodes .FormulaNodes)
        intro count count_checked
        unfold BoundedAnswer at count_checked
        split at count_checked
        next nodesFit =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := count_checked
          simp only [bind_ok]
          let updated : Work := {statistics := {work.statistics with operations := operation, input_formula_nodes := nodes}}
          have hc : ∀ f d s w, operation.val ≤ w.statistics.operations.val → StackValid s →
              s.active.val ≤ d.val → validate_formula f d signature scope s limits w
                ⦃ FormulaPost s (StackFormulaValid signature scope s f) w ⦄ := by
            intro f d s w hw hs hdepth
            exact ih (limits.max_operations.val - w.statistics.operations.val) (by omega) f d s w hs hdepth rfl
          cases formula with
          | True | False =>
            simp [FormulaPost, ValidationPost, StackFormulaValid, FormulaValid, stack_valid,
              stackFrame_refl, show work.statistics.operations.val ≤ operation.val by omega]
          | Atom symbol arguments =>
            have cast_eq : (UScalar.cast .Usize symbol).val = symbol.val := U32.cast_Usize_val_eq symbol
            dsimp only
            split
            next unknown =>
              simp only [spec_ok, FormulaPost, ValidationPost]
              refine ⟨stack_valid, stackFrame_refl stack, by omega, ?_⟩
              intro valid
              obtain ⟨⟨hknown, _⟩, _⟩ := valid
              have : ¬ symbol.val < signature.predicates.val.length := by scalar_tac
              omega
            next known =>
              have hi : (UScalar.cast .Usize symbol).val < signature.predicates.val.length := by scalar_tac
              rw [alloc.vec.Vec.index_slice_index]
              apply spec_bind (alloc.vec.Vec.index_usize_spec signature.predicates (UScalar.cast .Usize symbol) hi)
              intro arity harity
              subst arity
              split
              next wrongArity =>
                simp only [spec_ok, FormulaPost, ValidationPost]
                refine ⟨stack_valid, stackFrame_refl stack, by omega, ?_⟩
                intro valid
                obtain ⟨⟨hknown, equal⟩, _⟩ := valid
                have wrong : signature.predicates.val[(UScalar.cast .Usize symbol).val].val ≠ arguments.val.length := by scalar_tac
                simp [cast_eq, equal] at wrong
              next rightArity =>
                have arity : ArityMatches signature.predicates symbol arguments.val.length := by
                  refine ⟨by omega, ?_⟩
                  have equal : signature.predicates.val[(UScalar.cast .Usize symbol).val].val = arguments.val.length := by scalar_tac
                  simpa [cast_eq] using equal
                apply spec_bind (validate_formula_loop_spec arguments signature scope stack limits updated 0#usize stack_valid)
                rintro ⟨result, after⟩ ⟨hm, hp⟩
                simp only [Aeneas.Std.uncurry, spec_ok, FormulaPost]
                refine ⟨stack_valid, stackFrame_refl stack, ?_, ?_⟩
                · dsimp [updated] at hm; dsimp only; omega
                · cases result with
                  | Ok value =>
                    exact ⟨arity, fun i hi => (termValid_iff_scoped signature scope stack _).mp (hp i (by scalar_tac) hi)⟩
                  | Err error =>
                    cases error with
                    | Unsupported kind => exact hp
                    | Resource kind => exact Or.inl hp
                    | Invalid kind =>
                      intro valid
                      exact hp (fun i _ hi => (termValid_iff_scoped signature scope stack _).mpr (valid.2 i hi))
          | Not body =>
            apply spec_bind (Usize.add_spec (x := depth) (y := 1#usize) (by scalar_tac))
            intro deeper hd'
            apply spec_mono (hc body deeper stack updated (by simp [updated]) stack_valid (by scalar_tac))
            rintro ⟨result, afterstack, after⟩ ⟨validstack, frame, hm, hp⟩
            refine ⟨validstack, frame, ?_, hp⟩
            dsimp [updated] at hm; dsimp only; omega
          | And left right | Or left right | Implies left right =>
            apply spec_bind (Usize.add_spec (x := depth) (y := 1#usize) (by scalar_tac))
            intro deeper hd'
            apply spec_bind (hc left deeper stack updated (by simp [updated]) stack_valid (by scalar_tac))
            rintro ⟨result, middle, afterleft⟩ ⟨middle_valid, middle_frame, hm, hp⟩
            have hm' : operation.val ≤ afterleft.statistics.operations.val := by simpa [updated] using hm
            simp only [Aeneas.Std.uncurry]
            cases result with
            | Err error =>
              have post : FormulaPost stack
                  (StackFormulaValid signature scope stack left ∧ StackFormulaValid signature scope stack right)
                  work (.Err error, middle, afterleft) := by
                refine ⟨middle_valid, middle_frame, ?_, ?_⟩
                · dsimp only; omega
                · cases error with
                  | Unsupported kind => exact hp
                  | Resource kind => exact hp
                  | Invalid kind => exact fun valid => hp valid.1
              simpa [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                StackFormulaValid, FormulaValid] using post
            | Ok value =>
              simp only [bind_ok]
              have middle_depth : middle.active.val ≤ deeper.val := by have := middle_frame.1; scalar_tac
              apply spec_mono (hc right deeper middle afterleft hm' middle_valid middle_depth)
              rintro ⟨result, afterstack, after⟩ ⟨validstack, frame, hm2, hp2⟩
              refine ⟨validstack, stackFrame_trans middle_frame frame, ?_, ?_⟩
              · dsimp only at hm2 ⊢; omega
              · have same := stackFrame_formula middle_frame signature scope right
                cases result with
                | Ok value => exact ⟨hp, same.mp hp2⟩
                | Err error =>
                  cases error with
                  | Unsupported kind => exact hp2
                  | Resource kind => exact hp2
                  | Invalid kind => exact fun valid => hp2 (same.mpr valid.2)
          | Forall id body | Exists id body =>
            apply spec_bind (bounded_add_spec work.statistics.input_binders 1#usize
              (core.cmp.impls.OrdUsize.min limits.max_binders (UScalar.cast .Usize core.num.U32.MAX)) .Binders)
            intro bindercount binder_checked
            unfold BoundedAnswer at binder_checked
            split at binder_checked
            next bindersFit =>
              obtain ⟨binders, rfl, binders_eq⟩ := binder_checked
              simp only [bind_ok]
              apply spec_bind (bindings_push_spec stack { original := id, fresh := id } stack_valid (by scalar_tac))
              intro pushed ⟨pushed_valid, pushed_depth, pushed_entries⟩
              apply spec_bind (Usize.add_spec (x := depth) (y := 1#usize) (by scalar_tac))
              intro deeper hd'
              let under : Work := {statistics := {updated.statistics with input_binders := binders}}
              apply spec_bind (hc body deeper pushed under (by simp [under, updated]) pushed_valid (by scalar_tac))
              rintro ⟨result, inner, after⟩ ⟨inner_valid, inner_frame, hm, hp⟩
              apply spec_bind (bindings_pop_spec inner inner_valid)
              intro popped ⟨popped_valid, popped_depth, popped_entries⟩
              simp only [spec_ok, FormulaPost]
              refine ⟨popped_valid, popped_frame stack pushed inner popped { original := id, fresh := id }
                stack_valid pushed_depth pushed_entries inner_frame popped_depth popped_entries, ?_, ?_⟩
              · dsimp [under, updated] at hm; dsimp only; omega
              · have same := pushed_formula stack pushed id scope signature body stack_valid pushed_depth pushed_entries
                cases result with
                | Ok value => exact same.mp hp
                | Err error =>
                  cases error with
                  | Unsupported kind => exact hp
                  | Resource kind => exact hp
                  | Invalid kind => exact fun valid => hp (same.mpr valid)
            next bindersExceeded =>
              rw [binder_checked]
              simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                FormulaPost, ValidationPost, FormulaResource, stack_valid, stackFrame_refl,
                show work.statistics.operations.val ≤ operation.val by omega]
        next nodesExceeded =>
          rw [count_checked]
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            FormulaPost, ValidationPost, FormulaResource, stack_valid, stackFrame_refl,
            show work.statistics.operations.val ≤ operation.val by omega]
    next operationsExceeded =>
      rw [checked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        lift, FormulaPost, ValidationPost, FormulaResource, TermResource, stack_valid, stackFrame_refl]

end FangSkolemEmbeddedCore
