/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedCnfChecks

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core
variable {signature : Signature} {scope : VariableScope}
set_option maxRecDepth 2048



theorem append_cnf_spec (left right : Cnf)
    (leftGround : ∀ i (h : i < left.clauses.val.length), (ClauseScoped signature scope) left.clauses.val[i])
    (rightGround : ∀ i (h : i < right.clauses.val.length), (ClauseScoped signature scope) right.clauses.val[i])
    (limits : Limits) (work : Work) :
    append_cnf left right limits work ⦃ CnfPost (fun value =>
      value.clauses.val = left.clauses.val ++ right.clauses.val ∧
      value.literals.val = left.literals.val + right.literals.val ∧
      value.term_nodes.val = left.term_nodes.val + right.term_nodes.val ∧
      value.max_width.val = max left.max_width.val right.max_width.val) work ⦄ := by
  unfold append_cnf
  apply spec_bind (checked_add_spec (alloc.vec.Vec.len left.clauses) (alloc.vec.Vec.len right.clauses))
  intro answer guard
  cases answer
  case Err error =>
    cases error with
    | Invalid invalid => exact False.elim guard
    | Resource kind =>
      have typed : CnfResource kind := guard
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
  rename_i count
  dsimp only [CnfChecked] at guard
  have count_eq := guard
  simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply spec_bind (checked_add_spec left.literals right.literals)
  intro answer guard
  cases answer
  case Err error =>
    cases error with
    | Invalid invalid => exact False.elim guard
    | Resource kind =>
      have typed : CnfResource kind := guard
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
  rename_i literals
  dsimp only [CnfChecked] at guard
  have literals_eq := guard
  simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply spec_bind (checked_add_spec left.term_nodes right.term_nodes)
  intro answer guard
  cases answer
  case Err error =>
    cases error with
    | Invalid invalid => exact False.elim guard
    | Resource kind =>
      have typed : CnfResource kind := guard
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
  rename_i terms
  dsimp only [CnfChecked] at guard
  have terms_eq := guard
  simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  simp only [lift, bind_ok]
  apply spec_bind (check_shape_spec count literals (core.cmp.impls.OrdUsize.max left.max_width right.max_width) limits)
  intro answer guard
  cases answer
  case Err error =>
    cases error with
    | Invalid invalid => exact False.elim guard
    | Resource kind =>
      have typed : CnfResource kind := guard
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
  rename_i successful
  dsimp only [CnfChecked] at guard
  have shape := guard
  simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  apply spec_bind (check_storage_spec count literals terms limits work)
  intro answer guard
  cases answer
  case Err error =>
    cases error with
    | Invalid invalid => exact False.elim guard
    | Resource kind =>
      have typed : CnfResource kind := guard
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
  rename_i successful
  dsimp only [CnfChecked] at guard
  have storage := guard
  simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have capacity : left.clauses.val.length + right.clauses.val.length ≤ Usize.max := by
    have hc : count.val ≤ Usize.max := by scalar_tac
    have exactCount : count.val = left.clauses.val.length + right.clauses.val.length := by
      simpa using count_eq
    omega
  apply spec_bind (append_clauses_spec (alloc.vec.Vec.deref left.clauses) (alloc.vec.Vec.new _)
    (by simpa [alloc.vec.Vec.deref] using leftGround)
    (by simpa [alloc.vec.Vec.deref] using left.clauses.property) limits work)
  rintro ⟨answer, copied, updated⟩ ⟨hm, hp⟩
  dsimp only at hm hp
  simp only [Aeneas.Std.uncurry]
  cases answer with
  | Err error =>
    cases error with
    | Invalid kind => exact False.elim hp
    | Resource kind =>
      simpa [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked] using
        (show work.statistics.operations.val ≤ updated.statistics.operations.val ∧ CnfResource kind from ⟨hm, Or.inl hp⟩)
  | Ok successful =>
    have same : copied = left.clauses := by
      apply alloc.vec.Vec.ext
      simpa [alloc.vec.Vec.deref] using hp
    subst copied
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (append_clauses_spec (alloc.vec.Vec.deref right.clauses) left.clauses
      (by simpa [alloc.vec.Vec.deref] using rightGround)
      (by simpa [alloc.vec.Vec.deref] using capacity) limits updated)
    rintro ⟨answer, joined, after⟩ ⟨hm2, hp2⟩
    dsimp only at hm2 hp2
    simp only [Aeneas.Std.uncurry]
    cases answer with
    | Err error =>
      cases error with
      | Invalid kind => exact False.elim hp2
      | Resource kind =>
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked] using
          (show work.statistics.operations.val ≤ after.statistics.operations.val ∧ CnfResource kind from
            ⟨Nat.le_trans hm hm2, Or.inl hp2⟩)
    | Ok successful =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, spec_ok, CnfPost, CnfChecked]
      refine ⟨Nat.le_trans hm hm2, ?_, literals_eq, terms_eq, ?_⟩
      · simpa [alloc.vec.Vec.deref] using hp2
      · simp

theorem product_cnf_spec (left right : Cnf)
    (leftGround : ∀ i (h : i < left.clauses.val.length), (ClauseScoped signature scope) left.clauses.val[i])
    (rightGround : ∀ i (h : i < right.clauses.val.length), (ClauseScoped signature scope) right.clauses.val[i])
    (leftWidth : ∀ i (h : i < left.clauses.val.length), left.clauses.val[i].val.length ≤ left.max_width.val)
    (rightWidth : ∀ i (h : i < right.clauses.val.length), right.clauses.val[i].val.length ≤ right.max_width.val)
    (limits : Limits) (work : Work) :
    product_cnf left right limits work ⦃ CnfPost (fun value =>
      clauseLists value.clauses.val = rawProduct left.clauses.val right.clauses.val ∧
      (if left.clauses.val.length * right.clauses.val.length = 0 then
        value.literals.val = 0 ∧ value.term_nodes.val = 0 ∧ value.max_width.val = 0
      else
        value.literals.val = left.literals.val * right.clauses.val.length + right.literals.val * left.clauses.val.length ∧
        value.term_nodes.val = left.term_nodes.val * right.clauses.val.length + right.term_nodes.val * left.clauses.val.length ∧
        value.max_width.val = left.max_width.val + right.max_width.val)) work ⦄ := by
  unfold product_cnf
  apply spec_bind (checked_multiply_spec (alloc.vec.Vec.len left.clauses) (alloc.vec.Vec.len right.clauses))
  intro answer guard
  cases answer
  case Err error =>
    cases error with
    | Invalid invalid => exact False.elim guard
    | Resource kind =>
      have typed : CnfResource kind := guard
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
  rename_i count
  dsimp only [CnfChecked] at guard
  have count_eq := guard
  simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have count_val : count.val = left.clauses.val.length * right.clauses.val.length := by
    simpa using count_eq
  split
  next empty =>
    have product_empty : left.clauses.val.length * right.clauses.val.length = 0 := by
      simpa [empty] using count_val.symm
    have raw_empty : rawProduct left.clauses.val right.clauses.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [rawProduct_length, product_empty]
    simp [CnfPost, CnfChecked, clauseLists, product_empty, raw_empty]
  next nonempty =>
    have product_nonempty : left.clauses.val.length * right.clauses.val.length ≠ 0 := by
      intro zero
      have : count = 0#usize := by apply UScalar.eq_of_val_eq; simpa [zero] using count_val
      exact nonempty this
    apply spec_bind (checked_multiply_spec left.literals (alloc.vec.Vec.len right.clauses))
    intro answer guard
    cases answer
    case Err error =>
      cases error with
      | Invalid invalid => exact False.elim guard
      | Resource kind =>
        have typed : CnfResource kind := guard
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
    rename_i leftLiterals
    dsimp only [CnfChecked] at guard
    have leftLiterals_eq := guard
    simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (checked_multiply_spec right.literals (alloc.vec.Vec.len left.clauses))
    intro answer guard
    cases answer
    case Err error =>
      cases error with
      | Invalid invalid => exact False.elim guard
      | Resource kind =>
        have typed : CnfResource kind := guard
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
    rename_i rightLiterals
    dsimp only [CnfChecked] at guard
    have rightLiterals_eq := guard
    simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (checked_add_spec leftLiterals rightLiterals)
    intro answer guard
    cases answer
    case Err error =>
      cases error with
      | Invalid invalid => exact False.elim guard
      | Resource kind =>
        have typed : CnfResource kind := guard
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
    rename_i literals
    dsimp only [CnfChecked] at guard
    have literals_eq := guard
    simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (checked_multiply_spec left.term_nodes (alloc.vec.Vec.len right.clauses))
    intro answer guard
    cases answer
    case Err error =>
      cases error with
      | Invalid invalid => exact False.elim guard
      | Resource kind =>
        have typed : CnfResource kind := guard
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
    rename_i leftTerms
    dsimp only [CnfChecked] at guard
    have leftTerms_eq := guard
    simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (checked_multiply_spec right.term_nodes (alloc.vec.Vec.len left.clauses))
    intro answer guard
    cases answer
    case Err error =>
      cases error with
      | Invalid invalid => exact False.elim guard
      | Resource kind =>
        have typed : CnfResource kind := guard
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
    rename_i rightTerms
    dsimp only [CnfChecked] at guard
    have rightTerms_eq := guard
    simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (checked_add_spec leftTerms rightTerms)
    intro answer guard
    cases answer
    case Err error =>
      cases error with
      | Invalid invalid => exact False.elim guard
      | Resource kind =>
        have typed : CnfResource kind := guard
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
    rename_i terms
    dsimp only [CnfChecked] at guard
    have terms_eq := guard
    simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (checked_add_spec left.max_width right.max_width)
    intro answer guard
    cases answer
    case Err error =>
      cases error with
      | Invalid invalid => exact False.elim guard
      | Resource kind =>
        have typed : CnfResource kind := guard
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
    rename_i width
    dsimp only [CnfChecked] at guard
    have width_eq := guard
    simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (check_shape_spec count literals width limits)
    intro answer guard
    cases answer
    case Err error =>
      cases error with
      | Invalid invalid => exact False.elim guard
      | Resource kind =>
        have typed : CnfResource kind := guard
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
    rename_i successful
    dsimp only [CnfChecked] at guard
    have shape := guard
    simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (check_storage_spec count literals terms limits work)
    intro answer guard
    cases answer
    case Err error =>
      cases error with
      | Invalid invalid => exact False.elim guard
      | Resource kind =>
        have typed : CnfResource kind := guard
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked, typed]
    rename_i successful
    dsimp only [CnfChecked] at guard
    have storage := guard
    simp -failIfUnchanged only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    have capacity : left.clauses.val.length * right.clauses.val.length ≤ Usize.max := by
      rw [← count_val]
      scalar_tac
    have pairWidth : ∀ i (hi : i < left.clauses.val.length) j (hj : j < right.clauses.val.length),
        left.clauses.val[i].val.length + right.clauses.val[j].val.length ≤ Usize.max := by
      intro i hi j hj
      have hl := leftWidth i hi
      have hr := rightWidth j hj
      have hw : width.val ≤ Usize.max := by scalar_tac
      omega
    apply spec_mono (product_cnf_loop_spec left.clauses right.clauses leftGround rightGround pairWidth capacity
      limits work literals terms width (alloc.vec.Vec.new _) 0#usize (by simp [clauseLists, rawProduct]))
    rintro ⟨answer, after⟩ ⟨hm, hp⟩
    dsimp only at hm hp
    refine ⟨hm, ?_⟩
    cases answer with
    | Err error =>
      cases error with
      | Invalid kind => exact False.elim hp
      | Resource kind => exact Or.inl hp
    | Ok value =>
      rcases hp with ⟨lists, hl, ht, hw⟩
      simp only [CnfChecked, ite_eq_right product_nonempty, hl, ht, hw]
      refine ⟨lists, ?_, ?_, width_eq⟩
      · simpa [leftLiterals_eq, rightLiterals_eq] using literals_eq
      · simpa [leftTerms_eq, rightTerms_eq] using terms_eq

end FangScopedFof
