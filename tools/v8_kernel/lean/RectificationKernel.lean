/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact actual rectification for the two captured declarations. -/
import CoreCompositionKernel
import CoreRectifyCopyKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core.fang_quantified_fof_core
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

macro "reduce_rectification" : tactic => `(tactic|
  simp (disch := scalar_tac) [coreWork,
    fang_skolem_core.fang_quantified_fof_core.Work.tick,
    fang_skolem_core.fang_quantified_fof_core.Work.allocate,
    FangQuantifiedKernel.core_bounded_add,
    FangOriginalKernelProbe.add_value, FangOriginalKernelProbe.sub_value,
    FangQuantifiedKernel.checked_add_zero, core.option.Option.ok_or,
    fang_skolem_core.fang_quantified_fof_core.Bindings.push,
    fang_skolem_core.fang_quantified_fof_core.Bindings.pop,
    FangQuantifiedKernel.push_empty_slice, FangOriginalKernelProbe.push_empty,
    FangQuantifiedKernel.vector,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift])

theorem rectify_first_body (limits : Limits)
    (operations : 10 ≤ limits.max_operations.val) (allocated : 5 ≤ limits.max_stored_nodes.val) :
    rectify_formula firstFormula ⟨alloc.vec.Vec.new _, 0#usize⟩ 0#u32 limits
      (coreWork 5#usize 3#usize 1#usize 0#usize 1#usize) =
      .ok (.Ok firstFormula, zeroBinding 0#usize, 1#u32,
        coreWork 10#usize 3#usize 1#usize 5#usize 1#usize) := by
  have copy := renamed_variable_arguments 0#u32 0#u32 (zeroBinding 1#usize) limits
    (coreWork 8#usize 3#usize 1#usize 4#usize 1#usize)
    (coreWork 9#usize 3#usize 1#usize 4#usize 1#usize)
    (coreWork 9#usize 3#usize 1#usize 5#usize 1#usize)
    (coreWork 10#usize 3#usize 1#usize 5#usize 1#usize)
    (by reduce_core_ticks) (by reduce_core_ticks) (lookup_zero _ _ _ (by reduce_core_ticks))
  unfold firstFormula
  erw [rectify_formula]
  reduce_rectification
  erw [rectify_formula]
  reduce_rectification
  erw [rectify_formula]
  reduce_rectification
  simp only [deref_arguments]
  erw [copy]
  simp (disch := scalar_tac) [arguments, vector, zeroBinding, coreWork,
    sub_value, Aeneas.Std.uncurry]

theorem rectify_second_body (limits : Limits)
    (operations : 8 ≤ limits.max_operations.val) (allocated : 4 ≤ limits.max_stored_nodes.val) :
    rectify_formula secondFormula ⟨alloc.vec.Vec.new _, 0#usize⟩ 0#u32 limits
      (coreWork 4#usize 2#usize 1#usize 0#usize 1#usize) =
      .ok (.Ok secondFormula, zeroBinding 0#usize, 1#u32,
        coreWork 8#usize 2#usize 1#usize 4#usize 1#usize) := by
  have copy := renamed_variable_arguments 0#u32 0#u32 (zeroBinding 1#usize) limits
    (coreWork 6#usize 2#usize 1#usize 3#usize 1#usize)
    (coreWork 7#usize 2#usize 1#usize 3#usize 1#usize)
    (coreWork 7#usize 2#usize 1#usize 4#usize 1#usize)
    (coreWork 8#usize 2#usize 1#usize 4#usize 1#usize)
    (by reduce_core_ticks) (by reduce_core_ticks) (lookup_zero _ _ _ (by reduce_core_ticks))
  unfold secondFormula
  erw [rectify_formula]
  reduce_rectification
  erw [rectify_formula]
  reduce_rectification
  simp only [deref_arguments]
  erw [copy]
  simp (disch := scalar_tac) [arguments, vector, zeroBinding, coreWork,
    sub_value, Aeneas.Std.uncurry]

#print axioms FangQuantifiedKernel.rectify_first_body
#print axioms FangQuantifiedKernel.rectify_second_body
end FangQuantifiedKernel
