/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Actual generated polarity normalization at observed rectification boundaries. -/
import QuantifiedKernelValues
import CoreCopyKernel
import CoreArithmeticKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core.fang_quantified_fof_core
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def coreWork (operations formulaNodes termNodes allocated binders : Usize) :
    fang_skolem_core.fang_quantified_fof_core.Work :=
  ⟨⟨operations, formulaNodes, termNodes, allocated, 0#usize, 0#usize, 0#usize, binders⟩⟩

theorem deref_arguments : alloc.vec.Vec.deref arguments =
    Slice.from [.Var 0#u32] (by simp; scalar_tac) := by rfl

macro "reduce_core_ticks" : tactic => `(tactic|
  simp (disch := scalar_tac) [coreWork,
    fang_skolem_core.fang_quantified_fof_core.Work.tick,
    fang_skolem_core.fang_quantified_fof_core.Work.allocate,
    FangQuantifiedKernel.core_bounded_add,
    FangOriginalKernelProbe.add_value, FangOriginalKernelProbe.sub_value,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift])

theorem normalize_first (limits : fang_skolem_core.fang_quantified_fof_core.Limits)
    (operations : 14 ≤ limits.max_operations.val)
    (allocated : 8 ≤ limits.max_stored_nodes.val) :
    normalize_formula firstFormula true limits (coreWork 10#usize 3#usize 1#usize 5#usize 1#usize) =
      .ok (.Ok firstNnf, coreWork 14#usize 3#usize 1#usize 8#usize 1#usize) := by
  have copy := CoreCopy.variable_arguments 0#u32
    ⟨alloc.vec.Vec.new _, 0#usize⟩ limits
    (coreWork 13#usize 3#usize 1#usize 7#usize 1#usize)
    (coreWork 14#usize 3#usize 1#usize 7#usize 1#usize)
    (coreWork 14#usize 3#usize 1#usize 8#usize 1#usize)
    (by reduce_core_ticks) (by reduce_core_ticks)
  unfold firstFormula
  rw [normalize_formula]
  reduce_core_ticks
  rw [normalize_formula]
  reduce_core_ticks
  rw [normalize_formula]
  reduce_core_ticks
  simp only [Bindings.new, bind_ok, deref_arguments]
  erw [copy]
  simp [firstNnf, arguments, vector, coreWork, Aeneas.Std.uncurry]

theorem normalize_second (limits : fang_skolem_core.fang_quantified_fof_core.Limits)
    (operations : 11 ≤ limits.max_operations.val)
    (allocated : 7 ≤ limits.max_stored_nodes.val) :
    normalize_formula secondFormula true limits (coreWork 8#usize 2#usize 1#usize 4#usize 1#usize) =
      .ok (.Ok (.Exists 0#u32 (.Literal ⟨true, 0#u32, arguments⟩)),
        coreWork 11#usize 2#usize 1#usize 7#usize 1#usize) := by
  have copy := CoreCopy.variable_arguments 0#u32
    ⟨alloc.vec.Vec.new _, 0#usize⟩ limits
    (coreWork 10#usize 2#usize 1#usize 6#usize 1#usize)
    (coreWork 11#usize 2#usize 1#usize 6#usize 1#usize)
    (coreWork 11#usize 2#usize 1#usize 7#usize 1#usize)
    (by reduce_core_ticks) (by reduce_core_ticks)
  unfold secondFormula
  rw [normalize_formula]
  reduce_core_ticks
  rw [normalize_formula]
  reduce_core_ticks
  simp only [Bindings.new, bind_ok, deref_arguments]
  erw [copy]
  simp [arguments, vector, coreWork, Aeneas.Std.uncurry]

#print axioms FangQuantifiedKernel.normalize_first
#print axioms FangQuantifiedKernel.normalize_second
#print axioms FangQuantifiedKernel.deref_arguments
end FangQuantifiedKernel
