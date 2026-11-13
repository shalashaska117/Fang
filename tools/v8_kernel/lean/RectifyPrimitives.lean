/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import KernelPrimitives
import CoreCompositionKernel

open Aeneas Aeneas.Std
open Lean Meta Elab Tactic
open FangOriginalKernelProbe FangQuantifiedKernel
namespace FangKernelGenerator

theorem checked_add_value (left right : U32) (fits : left.val + right.val ≤ U32.max) :
    U32.checked_add left right = some (UScalar.ofNatCore (ty := .U32)
      (left.val + right.val) (by scalar_tac)) := by
  have specification := U32.checked_add_bv_spec left right
  cases result : U32.checked_add left right with
  | none => simp only [result] at specification; omega
  | some value =>
    simp only [result] at specification
    congr 1
    apply UScalar.eq_of_val_eq
    exact specification.2.1

#print axioms FangKernelGenerator.checked_add_value

macro "reduce_rectifier_primitives" : tactic => `(tactic|
  simp (disch := kernel_scalar) [
    FangOriginalKernelProbe.skolemLimits,
    FangKernelGenerator.checked_add_value, core.option.Option.ok_or, alloc.vec.Vec.deref,
    fang_skolem_core.fang_quantified_fof_core.Work.tick,
    fang_skolem_core.fang_quantified_fof_core.Work.allocate,
    FangQuantifiedKernel.core_bounded_add, FangQuantifiedKernel.u32_usize,
    core.cmp.impls.OrdUsize.min, U32.rMax,
    fang_skolem_core.fang_quantified_fof_core.Bindings.new,
    fang_skolem_core.fang_quantified_fof_core.Bindings.push,
    fang_skolem_core.fang_quantified_fof_core.Bindings.pop,
    FangKernelGenerator.push_from, FangKernelGenerator.index_from,
    FangQuantifiedKernel.u32_add_value,
    FangOriginalKernelProbe.add_value, FangOriginalKernelProbe.sub_value,
    FangQuantifiedKernel.vector, alloc.vec.Vec.val, alloc.vec.Vec.from,
    Slice.index_usize, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, lift])

elab "generated_rectifier" : tactic => do
  for _ in [:512] do
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    let saved ← Lean.Elab.Tactic.saveState
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTactic (← `(tactic| reduce_rectifier_primitives))
    catch _ => saved.restore
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    Lean.Elab.Tactic.evalTactic (← `(tactic| closed_generated_step))
  throwError "Generated kernel call-step budget exhausted"

end FangKernelGenerator
