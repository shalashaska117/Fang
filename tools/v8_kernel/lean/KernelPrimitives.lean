/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ClosedCall
import VectorKernel

open Aeneas Aeneas.Std
open Lean Meta Elab Tactic
open FangOriginalKernelProbe FangQuantifiedKernel
namespace FangKernelGenerator

elab "kernel_scalar" : tactic => do
  let target ← instantiateMVars (← getMainTarget)
  if target.hasFVar || target.hasMVar || target.hasLooseBVars then
    throwError "Arithmetic discharge requires a closed side condition"
  let code ← `(tactic|
    simp (config := { failIfUnchanged := false }) only
      [alloc.vec.Vec.val, Slice.from_val, List.length_cons, List.length_nil] <;>
      scalar_tac_preprocess <;> omega)
  Lean.Elab.Term.withoutErrToSorry <|
    Lean.Elab.Tactic.withoutRecover <| Lean.Elab.Tactic.evalTactic code

macro "reduce_generator_primitives" : tactic => `(tactic|
  simp (disch := kernel_scalar) [
    FangOriginalKernelProbe.skolemLimits,
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

elab "generated_kernel" : tactic => do
  for _ in [:512] do
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    let saved ← Lean.Elab.Tactic.saveState
    try
      Lean.Elab.Term.withoutErrToSorry <| Lean.Elab.Tactic.withoutRecover <|
        Lean.Elab.Tactic.evalTactic (← `(tactic| reduce_generator_primitives))
    catch _ => saved.restore
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    Lean.Elab.Tactic.evalTactic (← `(tactic| closed_generated_step))
  throwError "Generated kernel call-step budget exhausted"

end FangKernelGenerator
