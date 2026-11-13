/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compose the exact public Skolem call from the checked phase equations. -/
import DeclarationsTransformKernel
import DeclarationsValidationKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core
open SkolemWork
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem skolem_problem_exact : skolemize_problem declarations signature skolemLimits =
    .ok (.Ok transformed) := by
  have declarationsFit : ¬ Slice.len declarations > skolemLimits.max_declarations := by
    simp [declarations, skolemLimits]
  have functionsFit : ¬ alloc.vec.Vec.len signature.functions >
      core.cmp.impls.OrdUsize.min skolemLimits.max_functions
        (UScalar.cast .Usize core.num.U32.MAX) := by
    rw [function_cap]
    simp [signature, vector, alloc.vec.Vec.val]
  have functionsCopied := SkolemCopy.arities_empty skolemLimits (work 11#usize 0#usize)
  have predicatesCopied := SkolemCopy.arities_singleton 1#usize skolemLimits
    (work 11#usize 0#usize) (work 12#usize 0#usize) (work 12#usize 1#usize)
    (by reduce_skolem_work) (by reduce_skolem_work)
  unfold skolemize_problem
  rw [ite_eq_right declarationsFit]
  simp only [lift, bind_ok]
  rw [ite_eq_right functionsFit]
  simp only [Statistics.Insts.CoreDefaultDefault.default, default_value, bind_ok]
  erw [declarations_validated]
  simp only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry]
  erw [functionsCopied]
  simp only [bind_ok, Aeneas.Std.uncurry]
  erw [predicatesCopied]
  simp only [bind_ok, Aeneas.Std.uncurry]
  erw [transform_declarations_exact]
  simp only [bind_ok, Aeneas.Std.uncurry]
  rfl

#print axioms FangQuantifiedKernel.skolem_problem_exact
end FangQuantifiedKernel
