/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import NormalizationKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core.fang_quantified_fof_core
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def zeroBinding (active : Usize) : Bindings :=
  ⟨vector [⟨0#u32, 0#u32⟩] (by simp; scalar_tac), active⟩

theorem checked_add_zero : U32.checked_add 0#u32 1#u32 = some 1#u32 := by cbv

theorem lookup_zero (limits : Limits) (before after : Work)
    (tick : Work.tick before limits = .ok (.Ok (), after)) :
    lookup_binding 0#u32 (zeroBinding 1#usize) limits before = .ok (.Ok 0#u32, after) := by
  simp only [lookup_binding, zeroBinding]
  rw [lookup_binding_loop]
  simp (disch := scalar_tac) [tick, sub_value, index_singleton, vector,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry]

theorem renamed_variable_arguments (id fresh : U32) (stack : Bindings) (limits : Limits)
    (before ticked allocated after : Work)
    (tick : Work.tick before limits = .ok (.Ok (), ticked))
    (allocate : Work.allocate ticked 1#usize limits = .ok (.Ok (), allocated))
    (lookup : lookup_binding id stack limits allocated = .ok (.Ok fresh, after)) :
    copy_arguments (Slice.from [.Var id] (by simp; scalar_tac)) stack true limits before =
      .ok (.Ok (vector [.Var fresh] (by simp; scalar_tac)), after) := by
  simp only [copy_arguments]
  rw [copy_arguments_loop]
  simp (disch := scalar_tac) [Slice.index_usize]
  rw [copy_term]
  simp only [tick, allocate, lookup, bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, ↓reduceIte]
  simp (disch := scalar_tac) only [push_empty, add_value, bind_ok]
  rw [copy_arguments_loop]
  simp [vector]

#print axioms FangQuantifiedKernel.lookup_zero
#print axioms FangQuantifiedKernel.renamed_variable_arguments
#print axioms FangQuantifiedKernel.checked_add_zero
end FangQuantifiedKernel
