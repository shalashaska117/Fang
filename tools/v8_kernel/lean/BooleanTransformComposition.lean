/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import TransformComposition

open Aeneas Aeneas.Std
namespace FangKernelGenerator
open fang_skolem_core

theorem transform_and_of_parts {before intermediate after : Transformer} {limits : Limits}
    {left right leftValue rightValue : fang_quantified_fof_core.Nnf}
    {ticked allocated : Work}
    (tickRun : Work.tick before.work limits = .ok (.Ok (), ticked))
    (allocateRun : Work.allocate ticked 1#usize limits = .ok (.Ok (), allocated))
    (leftRun : Transformer.transform { before with work := allocated } left limits =
      .ok (.Ok leftValue, intermediate))
    (rightRun : Transformer.transform intermediate right limits =
      .ok (.Ok rightValue, after)) :
    Transformer.transform before (.And left right) limits =
      .ok (.Ok (.And leftValue rightValue), after) := by
  rw [Transformer.transform]
  simp only [tickRun, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, allocateRun, leftRun, rightRun]

theorem transform_or_of_parts {before intermediate after : Transformer} {limits : Limits}
    {left right leftValue rightValue : fang_quantified_fof_core.Nnf}
    {ticked allocated : Work}
    (tickRun : Work.tick before.work limits = .ok (.Ok (), ticked))
    (allocateRun : Work.allocate ticked 1#usize limits = .ok (.Ok (), allocated))
    (leftRun : Transformer.transform { before with work := allocated } left limits =
      .ok (.Ok leftValue, intermediate))
    (rightRun : Transformer.transform intermediate right limits =
      .ok (.Ok rightValue, after)) :
    Transformer.transform before (.Or left right) limits =
      .ok (.Ok (.Or leftValue rightValue), after) := by
  rw [Transformer.transform]
  simp only [tickRun, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, allocateRun, leftRun, rightRun]

#print axioms FangKernelGenerator.transform_and_of_parts
#print axioms FangKernelGenerator.transform_or_of_parts
end FangKernelGenerator
