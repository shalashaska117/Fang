/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compose actual generated calls at explicit quantifier boundaries. -/
import TransformPrimitives

open Aeneas Aeneas.Std
namespace FangKernelGenerator
open fang_skolem_core

theorem transform_forall_of_parts {before : Transformer} {limits : Limits} {id : U32}
    {body value : fang_quantified_fof_core.Nnf} {ticked allocated pushedWork : Work}
    {pushed popped : Universals} {changed : Transformer}
    (tickRun : Work.tick before.work limits = .ok (.Ok (), ticked))
    (allocateRun : Work.allocate ticked 1#usize limits = .ok (.Ok (), allocated))
    (pushRun : Universals.push before.universals id limits allocated =
      .ok (.Ok (), pushed, pushedWork))
    (childRun : Transformer.transform
      { before with universals := pushed, work := pushedWork } body limits =
      .ok (.Ok value, changed))
    (popRun : Universals.pop changed.universals = .ok popped) :
    Transformer.transform before (.Forall id body) limits =
      .ok (.Ok (.Forall id value), { changed with universals := popped }) := by
  rw [Transformer.transform]
  simp only [tickRun, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, allocateRun, pushRun, childRun, popRun]

theorem transform_exists_of_parts {before : Transformer} {limits : Limits} {id : U32}
    {body substituted value : fang_quantified_fof_core.Nnf} {ticked substitutedWork : Work}
    {replacement : fang.syntax.Term} {introduced after : Transformer}
    (tickRun : Work.tick before.work limits = .ok (.Ok (), ticked))
    (introduceRun : Transformer.introduce { before with work := ticked } id limits =
      .ok (.Ok replacement, introduced))
    (substituteRun : substitute_nnf body id replacement true limits introduced.work =
      .ok (.Ok substituted, substitutedWork))
    (childRun : Transformer.transform { introduced with work := substitutedWork }
      substituted limits = .ok (.Ok value, after)) :
    Transformer.transform before (.Exists id body) limits = .ok (.Ok value, after) := by
  rw [Transformer.transform]
  simp only [tickRun, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, introduceRun, substituteRun, childRun]

#print axioms FangKernelGenerator.transform_forall_of_parts
#print axioms FangKernelGenerator.transform_exists_of_parts
end FangKernelGenerator
