/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact arithmetic for the actual outer preprocessing counter. -/
import PublicNormalizationKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
namespace SkolemWork
open fang_skolem_core

def work (operations stored : Usize) : Work := ⟨⟨operations, stored⟩⟩

theorem bounded_add_value (left right cap : Usize) (kind : Resource)
    (fits : left.val + right.val ≤ cap.val) :
    bounded_add left right cap kind =
      .ok (.Ok (UScalar.ofNatCore (ty := .Usize) (left.val + right.val) (by scalar_tac))) := by
  rw [bounded_add, ite_eq_right (by scalar_tac)]
  rw [sub_value cap left (by scalar_tac)]
  simp only [bind_ok]
  rw [ite_eq_right (by scalar_tac), add_value left right (by scalar_tac)]
  simp only [bind_ok]

theorem remaining_value (operations stored : Usize)
    (operationsFit : operations.val ≤ 5000000) (storageFit : stored.val ≤ 1000000) :
    Work.remaining (work operations stored) skolemLimits =
      .ok (coreLimits
        (UScalar.ofNatCore (ty := .Usize) (5000000 - operations.val) (by scalar_tac))
        (UScalar.ofNatCore (ty := .Usize) (1000000 - stored.val) (by scalar_tac))) := by
  simp (disch := scalar_tac) [Work.remaining, work, skolemLimits, sub_value, coreLimits]

macro "reduce_skolem_work" : tactic => `(tactic|
  simp (disch := scalar_tac) [FangQuantifiedKernel.SkolemWork.work,
    fang_skolem_core.Work.tick, fang_skolem_core.Work.allocate, fang_skolem_core.Work.absorb,
    FangQuantifiedKernel.SkolemWork.bounded_add_value,
    FangOriginalKernelProbe.skolemLimits, FangOriginalKernelProbe.add_value,
    FangOriginalKernelProbe.sub_value, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.map_err, fang_skolem_core.P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    fang_skolem_core.Error.Core.constructor, Aeneas.Std.uncurry, lift])

#print axioms FangQuantifiedKernel.SkolemWork.bounded_add_value
#print axioms FangQuantifiedKernel.SkolemWork.remaining_value
end SkolemWork
end FangQuantifiedKernel
