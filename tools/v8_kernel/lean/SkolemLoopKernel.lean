/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compose exact equations for one iteration of the actual declaration loop. -/
import ExistentialTransformKernel

open Aeneas Aeneas.Std
namespace FangQuantifiedKernel
open fang_skolem_core

theorem declaration_step
    (input : Slice Declaration) (original : fang_quantified_fof_core.Signature)
    (limits : Limits) (before : Transformer)
    (formulas : alloc.vec.Vec fang_quantified_fof_core.Nnf)
    (declaration : Declaration) (ticked : Work)
    (remaining : fang_quantified_fof_core.Limits)
    (normalized : fang_quantified_fof_core.Normalized)
    (absorbed : Work) (value : fang_quantified_fof_core.Nnf) (changed : Transformer)
    (allocated : Work) (appended : alloc.vec.Vec fang_quantified_fof_core.Nnf)
    (next : Usize) (result : alloc.vec.Vec fang_quantified_fof_core.Nnf) (after : Transformer)
    (within : before.declaration < Slice.len input)
    (tickRun : Work.tick before.work limits = .ok (.Ok (), ticked))
    (indexRun : Slice.index_usize input before.declaration = .ok declaration)
    (remainingRun : Work.remaining ticked limits = .ok remaining)
    (normalizeRun : fang_quantified_fof_core.rectify_normalize_closed
      declaration.formula declaration.positive original remaining = .ok (.Ok normalized))
    (absorbRun : Work.absorb ticked normalized.statistics limits = .ok (.Ok (), absorbed))
    (transformRun : Transformer.transform { before with work := absorbed }
      normalized.formula limits = .ok (.Ok value, changed))
    (allocateRun : Work.allocate changed.work 1#usize limits = .ok (.Ok (), allocated))
    (pushRun : alloc.vec.Vec.push formulas value = .ok appended)
    (incrementRun : before.declaration + 1#usize = Result.ok next)
    (sameIndex : changed.declaration = before.declaration)
    (tailRun : transform_declarations_loop input original limits
      { changed with declaration := next, work := allocated } appended =
      .ok (.Ok result, after)) :
    transform_declarations_loop input original limits before formulas =
      .ok (.Ok result, after) := by
  rw [transform_declarations_loop, ite_eq_left within]
  simp only [tickRun, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry,
    indexRun, remainingRun, normalizeRun, core.result.Result.map_err,
    absorbRun, transformRun, allocateRun, pushRun, sameIndex, incrementRun, tailRun]

theorem declarations_finished
    (input : Slice Declaration) (original : fang_quantified_fof_core.Signature)
    (limits : Limits) (state : Transformer)
    (formulas : alloc.vec.Vec fang_quantified_fof_core.Nnf)
    (finished : ¬ state.declaration < Slice.len input) :
    transform_declarations_loop input original limits state formulas = .ok (.Ok formulas, state) := by
  rw [transform_declarations_loop, ite_eq_right finished]

#print axioms FangQuantifiedKernel.declaration_step
#print axioms FangQuantifiedKernel.declarations_finished
end FangQuantifiedKernel
