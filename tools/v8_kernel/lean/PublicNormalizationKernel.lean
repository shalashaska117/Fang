/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Composition through the actual public rectifier and normalizer. -/
import RectificationKernel

open Aeneas Aeneas.Std
namespace FangQuantifiedKernel
open fang_skolem_core.fang_quantified_fof_core

theorem rectify_first (operations stored : Usize)
    (enough : 10 ≤ operations.val) (storage : 5 ≤ stored.val) :
    rectify_closed firstFormula signature (coreLimits operations stored) =
      .ok (.Ok ⟨firstFormula, 1#u32,
        (coreWork 10#usize 3#usize 1#usize 5#usize 1#usize).statistics⟩) := by
  apply rectify_closed_of_parts firstFormula firstFormula signature (coreLimits operations stored)
    (coreWork 5#usize 3#usize 1#usize 0#usize 1#usize).statistics
    (zeroBinding 0#usize) 1#u32 (coreWork 10#usize 3#usize 1#usize 5#usize 1#usize)
  · exact validate_first operations stored (by omega)
  · exact rectify_first_body _ enough storage

theorem rectify_second (operations stored : Usize)
    (enough : 8 ≤ operations.val) (storage : 4 ≤ stored.val) :
    rectify_closed secondFormula signature (coreLimits operations stored) =
      .ok (.Ok ⟨secondFormula, 1#u32,
        (coreWork 8#usize 2#usize 1#usize 4#usize 1#usize).statistics⟩) := by
  apply rectify_closed_of_parts secondFormula secondFormula signature (coreLimits operations stored)
    (coreWork 4#usize 2#usize 1#usize 0#usize 1#usize).statistics
    (zeroBinding 0#usize) 1#u32 (coreWork 8#usize 2#usize 1#usize 4#usize 1#usize)
  · exact validate_second operations stored (by omega)
  · exact rectify_second_body _ enough storage

theorem normalization_first (operations stored : Usize)
    (enough : 14 ≤ operations.val) (storage : 8 ≤ stored.val) :
    rectify_normalize_closed firstFormula true signature (coreLimits operations stored) =
      .ok (.Ok ⟨firstNnf, (coreWork 14#usize 3#usize 1#usize 8#usize 1#usize).statistics⟩) := by
  have rectified := rectify_first operations stored (by omega) (by omega)
  have normalized := normalize_first (coreLimits operations stored) enough storage
  simp only [rectify_normalize_closed, rectified, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, normalized, Aeneas.Std.uncurry]

theorem normalization_second (operations stored : Usize)
    (enough : 11 ≤ operations.val) (storage : 7 ≤ stored.val) :
    rectify_normalize_closed secondFormula true signature (coreLimits operations stored) =
      .ok (.Ok ⟨.Exists 0#u32 (.Literal ⟨true, 0#u32, arguments⟩),
        (coreWork 11#usize 2#usize 1#usize 7#usize 1#usize).statistics⟩) := by
  have rectified := rectify_second operations stored (by omega) (by omega)
  have normalized := normalize_second (coreLimits operations stored) enough storage
  simp only [rectify_normalize_closed, rectified, bind_ok,
    core.result.Result.Insts.CoreOpsTry.branch, normalized, Aeneas.Std.uncurry]

#print axioms FangQuantifiedKernel.rectify_first
#print axioms FangQuantifiedKernel.rectify_second
#print axioms FangQuantifiedKernel.normalization_first
#print axioms FangQuantifiedKernel.normalization_second
end FangQuantifiedKernel
