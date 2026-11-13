/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import KernelPrimitives
import ClausifierCall
import QuantifiedClausifierKernel

open Aeneas Aeneas.Std
open Lean Meta Elab Tactic
namespace FangKernelGenerator

macro "reduce_clause_primitives" : tactic => `(tactic|
  simp (disch := kernel_scalar) [
    FangQuantifiedKernel.Clausifier.limits, FangOriginalReplay.initialStatistics,
    fang_fof_core.Work.tick, fang_fof_core.Work.allocate,
    FangQuantifiedKernel.Clausifier.bounded_add_value,
    fang_fof_core.check_shape, fang_fof_core.singleton,
    FangKernelGenerator.push_from, FangKernelGenerator.index_from,
    FangOriginalKernelProbe.add_value, FangOriginalKernelProbe.sub_value,
    FangQuantifiedKernel.vector, alloc.vec.Vec.val, alloc.vec.Vec.from,
    alloc.vec.Vec.deref, Slice.index_usize,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift])

elab "generated_clausifier" : tactic => do
  for _ in [:512] do
    if (← getGoals).isEmpty then return
    let saved ← saveState
    try
      Lean.Elab.Term.withoutErrToSorry <| withoutRecover <|
        evalTactic (← `(tactic| reduce_clause_primitives))
    catch _ => saved.restore
    if (← getGoals).isEmpty then return
    let reduced ← saveState
    try
      Lean.Elab.Term.withoutErrToSorry <| withoutRecover <|
        evalTactic (← `(tactic| first | rfl | (apply UScalar.eq_of_val_eq; rfl)))
    catch _ => reduced.restore
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| closed_clausifier_step))
  throwError "Generated clausifier call-step budget exhausted"

end FangKernelGenerator
