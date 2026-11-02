/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import SkolemPrimitives
import MutableVectorKernel

open Aeneas Aeneas.Std
open Lean Meta Elab Tactic
open FangOriginalKernelProbe FangQuantifiedKernel
namespace FangKernelGenerator

macro "reduce_transform_primitives" : tactic => `(tactic|
  simp (disch := kernel_scalar) [
    FangOriginalKernelProbe.skolemLimits,
    FangKernelGenerator.index_mut_value, FangKernelGenerator.usize_u32, alloc.vec.Vec.set,
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

elab "generated_transform" : tactic => do
  for _ in [:512] do
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    let saved ← Lean.Elab.Tactic.saveState
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTactic (← `(tactic| reduce_transform_primitives))
    catch _ => saved.restore
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    Lean.Elab.Tactic.evalTactic (← `(tactic| closed_skolem_step))
  throwError "Generated kernel call-step budget exhausted"

end FangKernelGenerator
