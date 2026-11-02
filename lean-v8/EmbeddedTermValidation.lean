import EmbeddedTermScope

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

def TermsFrom (signature : Signature) (scope : VariableScope) (stack : Bindings) (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
    (index : Nat) : Prop :=
  ∀ i, index ≤ i → ∀ h : i < arguments.val.length, TermValid signature scope stack arguments.val[i]

def TermResource (kind : Resource) : Prop :=
  kind = .Operations ∨ kind = .TermDepth ∨ kind = .InputTermNodes

/-- Resource failure makes no statement about validity. Invalid failure excludes it. -/
def ValidationPost (valid : Prop) (resource : Resource → Prop) (before : Work)
    (answer : core.result.Result Unit fang_skolem_core.fang_quantified_fof_core.Error × Work) : Prop :=
  before.statistics.operations.val ≤ answer.2.statistics.operations.val ∧
    match answer.1 with
    | .Ok _ => valid
    | .Err (.Invalid _) => ¬ valid
    | .Err (.Resource kind) => resource kind
    | .Err (.Unsupported _) => False

theorem validate_term_loop_spec (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
    (depth : Usize) (signature : Signature) (scope : VariableScope) (stack : Bindings) (limits : Limits) (stack_valid : StackValid stack) (bound : Nat)
    (child : ∀ term depth work, bound ≤ work.statistics.operations.val →
      validate_term term depth signature scope stack limits work
        ⦃ ValidationPost (TermValid signature scope stack term) TermResource work ⦄)
    (work : Work) (index : Usize) (hb : bound ≤ work.statistics.operations.val)
    (hd : depth.val ≤ 64) :
    validate_term_loop arguments depth signature.functions signature.predicates scope stack
      limits.max_formula_depth limits.max_formula_nodes limits.max_term_depth
      limits.max_input_term_nodes limits.max_clauses limits.max_literals_per_clause
      limits.max_literals limits.max_stored_nodes limits.max_operations limits.max_binders work index
      ⦃ ValidationPost (TermsFrom signature scope stack arguments index.val) TermResource work ⦄ := by
  unfold validate_term_loop
  dsimp only
  split
  next hindex =>
    have hlt : index.val < arguments.val.length := by scalar_tac
    rw [alloc.vec.Vec.index_slice_index]
    apply spec_bind (alloc.vec.Vec.index_usize_spec arguments index hlt)
    intro term ht
    subst term
    apply spec_bind (Usize.add_spec (x := depth) (y := 1#usize) (by scalar_tac))
    intro deeper hdepth
    apply spec_bind (child arguments.val[index.val] deeper work hb)
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
      apply spec_mono (validate_term_loop_spec arguments depth signature scope stack limits stack_valid bound child
        updated next (by omega) hd)
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
        | Invalid kind =>
          exact fun valid => hc2 (fun i hi hi' => valid i (by omega) hi')
  next hindex =>
    simp only [spec_ok, ValidationPost]
    refine ⟨Nat.le_refl _, ?_⟩
    intro i hi hi'
    have : arguments.val.length ≤ index.val := by scalar_tac
    omega
termination_by arguments.val.length - index.val
decreasing_by omega

theorem validate_term_spec (term : fang_skolem_core.fang.syntax.Term) (depth : Usize)
    (signature : Signature) (scope : VariableScope) (stack : Bindings) (limits : Limits) (work : Work) (stack_valid : StackValid stack) :
    validate_term term depth signature scope stack limits work
      ⦃ ValidationPost (TermValid signature scope stack term) TermResource work ⦄ := by
  generalize hn : limits.max_operations.val - work.statistics.operations.val = n
  induction n using Nat.strong_induction_on generalizing term depth work with
  | h n ih =>
    unfold validate_term
    apply spec_bind (tick_spec work limits)
    intro answer checked
    unfold TickAnswer at checked
    split at checked
    next fits =>
      obtain ⟨operation, rfl, operation_eq⟩ := checked
      simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift]
      split
      next depthExceeded =>
        simp only [spec_ok, ValidationPost, TermResource]
        exact ⟨by omega, Or.inr (Or.inl trivial)⟩
      next depthWithin =>
        have hd : depth.val ≤ 64 := by scalar_tac
        apply spec_bind (bounded_add_spec work.statistics.input_term_nodes 1#usize
          limits.max_input_term_nodes .InputTermNodes)
        intro count count_checked
        unfold BoundedAnswer at count_checked
        split at count_checked
        next nodesFit =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := count_checked
          simp only [bind_ok]
          let updated : Work := {statistics := {work.statistics with operations := operation, input_term_nodes := nodes}}
          have hc : ∀ t d w, operation.val ≤ w.statistics.operations.val →
              validate_term t d signature scope stack limits w
                ⦃ ValidationPost (TermValid signature scope stack t) TermResource w ⦄ := by
            intro t d w hw
            exact ih (limits.max_operations.val - w.statistics.operations.val) (by omega) t d w rfl
          cases term with
          | Var varId =>
            apply spec_bind (bound_name_spec varId stack limits updated stack_valid)
            rintro ⟨answer, after⟩ ⟨monotone, recognized⟩
            have total_monotone : work.statistics.operations.val ≤ after.statistics.operations.val := by
              dsimp [updated] at monotone
              omega
            dsimp only at recognized
            simp only [Aeneas.Std.uncurry]
            cases answer with
            | Err error =>
              have post : ValidationPost (TermValid signature scope stack (.Var varId)) TermResource work
                  (.Err error, after) := by
                refine ⟨total_monotone, ?_⟩
                cases error with
                | Resource kind => exact Or.inl recognized
                | Invalid kind => exact False.elim recognized
                | Unsupported kind => exact recognized
              simpa [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
            | Ok found =>
              simp only [bind_ok]
              cases found with
              | true =>
                simp only [ite_true, spec_ok, ValidationPost, termValid_var]
                exact ⟨total_monotone, Or.inl recognized⟩
              | false =>
                simp only [Bool.false_eq_true, ite_false]
                have absent : ¬ (lookupPrefix varId stack.entries.val stack.active.val).isSome = true := by
                  rw [recognized]
                  decide
                cases scope with
                | Ground =>
                  simp [ValidationPost, VariableValid, OuterValid, absent, total_monotone]
                | Bound count =>
                  dsimp only
                  split
                  next within =>
                    simp only [spec_ok, ValidationPost, termValid_var, VariableValid, absent, OuterValid]
                    exact ⟨total_monotone, by scalar_tac⟩
                  next outside =>
                    simp only [spec_ok, ValidationPost, termValid_var, VariableValid, absent, OuterValid]
                    exact ⟨total_monotone, by scalar_tac⟩
          | Fun symbol arguments =>
            have cast_eq : (UScalar.cast .Usize symbol).val = symbol.val := by
              exact U32.cast_Usize_val_eq symbol
            dsimp only
            split
            next unknown =>
              simp only [spec_ok, ValidationPost]
              refine ⟨by omega, ?_⟩
              intro valid
              obtain ⟨⟨hknown, _⟩, _⟩ := (termValid_fun signature scope stack symbol arguments).mp valid
              have : ¬ symbol.val < signature.functions.val.length := by scalar_tac
              omega
            next known =>
              have hi : (UScalar.cast .Usize symbol).val < signature.functions.val.length := by scalar_tac
              rw [alloc.vec.Vec.index_slice_index]
              apply spec_bind (alloc.vec.Vec.index_usize_spec signature.functions (UScalar.cast .Usize symbol) hi)
              intro arity harity
              subst arity
              split
              next wrongArity =>
                simp only [spec_ok, ValidationPost]
                refine ⟨by omega, ?_⟩
                intro valid
                obtain ⟨⟨hknown, equal⟩, _⟩ := (termValid_fun signature scope stack symbol arguments).mp valid
                have wrong : signature.functions.val[(UScalar.cast .Usize symbol).val].val ≠ arguments.val.length := by scalar_tac
                simp [cast_eq, equal] at wrong
              next rightArity =>
                have arity : ArityMatches signature.functions symbol arguments.val.length := by
                  refine ⟨by omega, ?_⟩
                  have equal : signature.functions.val[(UScalar.cast .Usize symbol).val].val = arguments.val.length := by scalar_tac
                  simpa [cast_eq] using equal
                apply spec_mono (validate_term_loop_spec arguments depth signature scope stack limits stack_valid operation.val hc
                  updated 0#usize (by simp [updated]) hd)
                rintro ⟨result, after⟩ ⟨hm, hp⟩
                dsimp only at hm hp
                refine ⟨by dsimp only; dsimp [updated] at hm; omega, ?_⟩
                cases result with
                | Ok value => exact (termValid_fun signature scope stack symbol arguments).mpr ⟨arity, fun i hi => hp i (by scalar_tac) hi⟩
                | Err error =>
                  cases error with
                  | Unsupported kind => exact hp
                  | Resource kind => exact hp
                  | Invalid kind =>
                    intro valid
                    exact hp (fun i _ hi => ((termValid_fun signature scope stack symbol arguments).mp valid).2 i hi)
        next nodesExceeded =>
          rw [count_checked]
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            ValidationPost, TermResource] using (show work.statistics.operations.val ≤ operation.val by omega)
    next operationsExceeded =>
      rw [checked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        lift, ValidationPost, TermResource]


end FangSkolemEmbeddedCore
