/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RectifyPrimitives
import SkolemCall

open Aeneas Aeneas.Std
open Lean Meta Elab Tactic
open FangOriginalKernelProbe FangQuantifiedKernel
namespace FangKernelGenerator

theorem skolem_bounded_add (left right cap : Usize)
    (kind : fang_skolem_core.Resource)
    (fits : left.val + right.val ≤ cap.val) :
    fang_skolem_core.bounded_add left right cap kind =
      .ok (.Ok (UScalar.ofNatCore (ty := .Usize) (left.val + right.val) (by scalar_tac))) := by
  rw [fang_skolem_core.bounded_add, ite_eq_right (by scalar_tac)]
  rw [sub_value cap left (by scalar_tac)]
  simp only [bind_ok]
  rw [ite_eq_right (by scalar_tac), add_value left right (by scalar_tac)]
  simp only [bind_ok]

#print axioms FangKernelGenerator.skolem_bounded_add

macro "reduce_skolem_primitives" : tactic => `(tactic|
  simp (disch := kernel_scalar) [
    FangOriginalKernelProbe.skolemLimits,
    fang_skolem_core.Work.tick, fang_skolem_core.Work.allocate,
    fang_skolem_core.Work.remaining, fang_skolem_core.Work.absorb,
    FangKernelGenerator.skolem_bounded_add,
    fang_skolem_core.Universals.push, fang_skolem_core.Universals.pop,
    fang_skolem_core.fang_quantified_fof_core.Work.new,
    FangOriginalKernelProbe.core_statistics_eq,
    core.result.Result.map_err, fang_skolem_core.Error.Core.constructor,
    fang_skolem_core.P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
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

elab "generated_skolem" : tactic => do
  for _ in [:512] do
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    let saved ← Lean.Elab.Tactic.saveState
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTactic (← `(tactic| reduce_skolem_primitives))
    catch _ => saved.restore
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    Lean.Elab.Tactic.evalTactic (← `(tactic| closed_skolem_step))
  throwError "Generated kernel call-step budget exhausted"

end FangKernelGenerator
