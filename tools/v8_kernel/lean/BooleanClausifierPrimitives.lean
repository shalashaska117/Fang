/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ClausifierPrimitives
import BooleanClausifierCall

open Aeneas Aeneas.Std
open Lean Meta Elab Tactic
namespace FangKernelGenerator

theorem usize_checked_add_value (left right : Usize)
    (fits : left.val + right.val ≤ Usize.max) :
    Usize.checked_add left right = some (UScalar.ofNatCore (ty := .Usize)
      (left.val + right.val) (by scalar_tac)) := by
  have specification := Usize.checked_add_bv_spec left right
  cases result : Usize.checked_add left right with
  | none => simp only [result] at specification; omega
  | some value =>
    simp only [result] at specification
    congr 1
    apply UScalar.eq_of_val_eq
    exact specification.2.1

theorem usize_checked_mul_value (left right : Usize)
    (fits : left.val * right.val ≤ Usize.max) :
    Usize.checked_mul left right = some (UScalar.ofNatCore (ty := .Usize)
      (left.val * right.val) (by scalar_tac)) := by
  have specification := Usize.checked_mul_bv_spec left right
  cases result : Usize.checked_mul left right with
  | none => simp only [result] at specification; omega
  | some value =>
    simp only [result] at specification
    congr 1
    apply UScalar.eq_of_val_eq
    exact specification.2.1

#print axioms FangKernelGenerator.usize_checked_add_value
#print axioms FangKernelGenerator.usize_checked_mul_value

macro "reduce_boolean_clause_primitives" : tactic => `(tactic|
  simp (disch := kernel_scalar) [
    FangQuantifiedKernel.Clausifier.limits, FangOriginalReplay.initialStatistics,
    fang_fof_core.Work.tick, fang_fof_core.Work.allocate,
    FangQuantifiedKernel.Clausifier.bounded_add_value,
    fang_fof_core.check_shape, fang_fof_core.singleton, fang_fof_core.check_storage,
    fang_fof_core.add, fang_fof_core.multiply,
    FangKernelGenerator.usize_checked_add_value, FangKernelGenerator.usize_checked_mul_value,
    core.option.Option.ok_or, core.cmp.impls.OrdUsize.max,
    FangKernelGenerator.push_from, FangKernelGenerator.index_from,
    FangOriginalKernelProbe.add_value, FangOriginalKernelProbe.sub_value,
    FangQuantifiedKernel.vector, alloc.vec.Vec.val, alloc.vec.Vec.from,
    alloc.vec.Vec.deref, Slice.index_usize,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift])

elab "generated_boolean_clausifier" : tactic => do
  for _ in [:512] do
    if (← getGoals).isEmpty then return
    let saved ← saveState
    try
      Lean.Elab.Term.withoutErrToSorry <| withoutRecover <|
        evalTactic (← `(tactic| reduce_boolean_clause_primitives))
    catch _ => saved.restore
    if (← getGoals).isEmpty then return
    let reduced ← saveState
    try
      Lean.Elab.Term.withoutErrToSorry <| withoutRecover <|
        evalTactic (← `(tactic| first | rfl | (apply UScalar.eq_of_val_eq; rfl)))
    catch _ => reduced.restore
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| closed_boolean_clausifier_step))
  throwError "Generated Boolean clausifier call-step budget exhausted"

end FangKernelGenerator
