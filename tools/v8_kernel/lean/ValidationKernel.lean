/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact actual validation of the two quantified fixture declarations. -/
import QuantifiedKernelValues
import CoreArithmeticKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core.fang_quantified_fof_core
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def coreLimits (operations stored : Usize) : fang_skolem_core.fang_quantified_fof_core.Limits :=
  { skolemLimits.core with max_operations := operations, max_stored_nodes := stored }

macro "reduce_validation" : tactic => `(tactic|
  simp (disch := scalar_tac) [FangQuantifiedKernel.coreLimits,
    FangOriginalKernelProbe.skolemLimits,
    fang_skolem_core.fang_quantified_fof_core.Work.tick,
    FangQuantifiedKernel.core_bounded_add,
    FangQuantifiedKernel.u32_usize,
    core.cmp.impls.OrdUsize.min, U32.rMax,
    fang_skolem_core.fang_quantified_fof_core.Bindings.new,
    fang_skolem_core.fang_quantified_fof_core.Bindings.push,
    fang_skolem_core.fang_quantified_fof_core.Bindings.pop,
    FangOriginalKernelProbe.push_empty, FangOriginalKernelProbe.add_value,
    FangQuantifiedKernel.push_empty_slice, FangQuantifiedKernel.vector,
    FangQuantifiedKernel.index_singleton,
    FangOriginalKernelProbe.sub_value, alloc.vec.Vec.val, alloc.vec.Vec.from,
    Slice.index_usize, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, lift])

theorem validate_first (operations stored : Usize) (enough : 5 ≤ operations.val) :
    validate firstFormula signature (coreLimits operations stored) =
      .ok (.Ok ⟨5#usize, 3#usize, 1#usize, 0#usize, 0#usize, 0#usize, 0#usize, 1#usize⟩) := by
  simp only [validate, validate_with_scope, Work.new, core_statistics_eq,
    Bindings.new, bind_ok]
  unfold firstFormula
  erw [validate_formula]
  reduce_validation
  erw [validate_formula]
  reduce_validation
  erw [validate_formula]
  simp only [signature, arguments, vector]
  reduce_validation
  erw [validate_formula_loop]
  reduce_validation
  erw [validate_term]
  reduce_validation
  erw [bound_name, bound_name_loop]
  reduce_validation
  erw [validate_formula_loop]
  reduce_validation

theorem validate_second (operations stored : Usize) (enough : 4 ≤ operations.val) :
    validate secondFormula signature (coreLimits operations stored) =
      .ok (.Ok ⟨4#usize, 2#usize, 1#usize, 0#usize, 0#usize, 0#usize, 0#usize, 1#usize⟩) := by
  simp only [validate, validate_with_scope, Work.new, core_statistics_eq,
    Bindings.new, bind_ok]
  unfold secondFormula
  erw [validate_formula]
  reduce_validation
  erw [validate_formula]
  simp only [signature, arguments, vector]
  reduce_validation
  erw [validate_formula_loop]
  reduce_validation
  erw [validate_term]
  reduce_validation
  erw [bound_name, bound_name_loop]
  reduce_validation
  erw [validate_formula_loop]
  reduce_validation

#print axioms FangQuantifiedKernel.validate_first
#print axioms FangQuantifiedKernel.validate_second
end FangQuantifiedKernel
