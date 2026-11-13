/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Primitive reductions for actual removal calls; no replacement algorithm. -/
import KernelPrimitives
import RemovalCall
import OriginalReplay

open Aeneas Aeneas.Std
open Lean Meta Elab Tactic
namespace FangKernelGenerator

def removalLimits : fang_binder_removal_core.Limits := {
  max_formula_depth := 64#usize, max_operations := 5000000#usize,
  max_output_nodes := 1000000#usize }

macro "reduce_removal_primitives" : tactic => `(tactic|
  simp (disch := kernel_scalar) [
    FangKernelGenerator.removalLimits, fang_binder_removal_core.increment,
    core.cmp.impls.OrdUsize.min, FangOriginalKernelProbe.add_value,
    FangQuantifiedKernel.vector, alloc.vec.Vec.val,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift])

elab "generated_removal" : tactic => do
  for _ in [:512] do
    if (← getGoals).isEmpty then return
    let saved ← saveState
    try
      Lean.Elab.Term.withoutErrToSorry <| withoutRecover <|
        evalTactic (← `(tactic| reduce_removal_primitives))
    catch _ => saved.restore
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| closed_removal_step))
  throwError "Generated removal call-step budget exhausted"

end FangKernelGenerator
