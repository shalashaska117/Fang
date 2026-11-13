/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Successful public validation exposes the actual body call used by rectification. -/
import DeclarationsTrace
import ValidationKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core.fang_quantified_fof_core

theorem validation_body_of_success (formula : Formula) (sig : Signature) (limits : Limits)
    (statistics : Statistics) (accepted : validate formula sig limits = .ok (.Ok statistics)) :
    ∃ stack, validate_formula formula 1#usize sig .Ground
      ⟨alloc.vec.Vec.new _, 0#usize⟩ limits
      ⟨⟨0#usize, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize⟩⟩ =
      .ok (.Ok (), stack, ⟨statistics⟩) := by
  simp only [validate, validate_with_scope, Work.new, core_statistics_eq,
    Bindings.new, bind_ok] at accepted
  obtain ⟨⟨answer, stack, work⟩, body, tail⟩ := (FangSkolemCore.bind_success_iff _ _ _).mp accepted
  cases answer with
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      Aeneas.Std.uncurry] at tail
  | Ok value =>
    cases value
    simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      Result.ok.injEq, core.result.Result.Ok.injEq] at tail
    cases work
    cases tail
    exact ⟨stack, body⟩

theorem rectify_closed_of_parts (formula output : Formula) (sig : Signature) (limits : Limits)
    (statistics : Statistics) (stack : Bindings) (next : U32) (after : Work)
    (validated : validate formula sig limits = .ok (.Ok statistics))
    (rectified : rectify_formula formula ⟨alloc.vec.Vec.new _, 0#usize⟩ 0#u32 limits ⟨statistics⟩ =
      .ok (.Ok output, stack, next, after)) :
    rectify_closed formula sig limits = .ok (.Ok ⟨output, next, after.statistics⟩) := by
  obtain ⟨ignored, body⟩ := validation_body_of_success formula sig limits statistics validated
  simp only [rectify_closed, Work.new, core_statistics_eq, Bindings.new, bind_ok, body,
    Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, rectified]

#print axioms FangQuantifiedKernel.validation_body_of_success
#print axioms FangQuantifiedKernel.rectify_closed_of_parts
end FangQuantifiedKernel
