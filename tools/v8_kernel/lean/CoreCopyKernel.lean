/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact composition at one known generated variable-copy call. -/
import QuantifiedKernelPrimitives

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
namespace CoreCopy
open fang_skolem_core.fang_quantified_fof_core
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem variable_arguments (id : U32) (stack : Bindings) (limits : Limits)
    (before ticked after : Work)
    (tick : Work.tick before limits = .ok (.Ok (), ticked))
    (allocate : Work.allocate ticked 1#usize limits = .ok (.Ok (), after)) :
    copy_arguments (Slice.from [.Var id] (by simp; scalar_tac)) stack false limits before =
      .ok (.Ok (vector [.Var id] (by simp; scalar_tac)), after) := by
  simp only [copy_arguments]
  rw [copy_arguments_loop]
  simp (disch := scalar_tac) [Slice.index_usize]
  rw [copy_term]
  simp only [tick, allocate, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, Bool.false_eq_true, ↓reduceIte]
  simp (disch := scalar_tac) only [push_empty, add_value, bind_ok]
  rw [copy_arguments_loop]
  simp [vector]

#print axioms FangQuantifiedKernel.CoreCopy.variable_arguments
end CoreCopy
end FangQuantifiedKernel
