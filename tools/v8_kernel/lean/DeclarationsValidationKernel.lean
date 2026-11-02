/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The actual outer validation loop over the two captured declarations. -/
import SkolemWorkKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core
open SkolemWork
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem declarations_validated :
    validate_declarations declarations signature skolemLimits (work 0#usize 0#usize) =
      .ok (.Ok (), work 11#usize 0#usize) := by
  simp only [validate_declarations]
  erw [validate_declarations_loop]
  simp only [declarations]
  simp (disch := scalar_tac) [Slice.index_usize]
  reduce_skolem_work
  erw [remaining_value]
  · simp only [bind_ok]
    erw [validate_first 4999999#usize 1000000#usize (by scalar_tac)]
    reduce_skolem_work
    erw [validate_declarations_loop]
    simp (disch := scalar_tac) [Slice.index_usize]
    reduce_skolem_work
    erw [remaining_value]
    · simp only [bind_ok]
      erw [validate_second 4999993#usize 1000000#usize (by scalar_tac)]
      reduce_skolem_work
      erw [validate_declarations_loop]
      simp
    · scalar_tac
    · scalar_tac
  · scalar_tac
  · scalar_tac

#print axioms FangQuantifiedKernel.declarations_validated
end FangQuantifiedKernel
