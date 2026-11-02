/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Literal-preserving equations for the actual universal-binder remover. -/
import QuantifiedKernelValues
import OriginalReplay

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_binder_removal_core
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def removalLimits : Limits := {
  max_formula_depth := 64#usize, max_operations := 5000000#usize,
  max_output_nodes := 1000000#usize }

theorem remove_literal_exact (literal : fang.syntax.Literal) :
    remove_universals (.Literal literal) removalLimits =
      .ok (.Ok ⟨.Literal literal, ⟨1#usize, 1#usize⟩⟩) := by
  unfold remove_universals
  rw [remove]
  simp (disch := scalar_tac) [increment, removalLimits, add_value,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift]

theorem remove_forall_literal_exact (binder : U32) (literal : fang.syntax.Literal) :
    remove_universals (.Forall binder (.Literal literal)) removalLimits =
      .ok (.Ok ⟨.Literal literal, ⟨2#usize, 1#usize⟩⟩) := by
  unfold remove_universals
  rw [remove]
  simp (disch := scalar_tac) [increment, removalLimits, add_value,
    core.result.Result.Insts.CoreOpsTry.branch, lift]
  erw [remove]
  simp (disch := scalar_tac) [increment, add_value,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift]

#print axioms FangQuantifiedKernel.remove_literal_exact
#print axioms FangQuantifiedKernel.remove_forall_literal_exact
end FangQuantifiedKernel
