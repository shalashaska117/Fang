/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact substitution and transformation after the captured Skolem introduction. -/
import ExistentialIntroKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core
open SkolemWork
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def secondAfter : Transformer := { afterIntroduction with work := work 50#usize 28#usize }

theorem substitute_constant :
    substitute_nnf (.Literal ⟨true, 0#u32, arguments⟩) 0#u32 freshConstant true skolemLimits
      (work 45#usize 24#usize) = .ok (.Ok secondNnf, work 48#usize 26#usize) := by
  have copied := SkolemCopy.constant_term 0#u32
    (work 47#usize 25#usize) (work 48#usize 25#usize) (work 48#usize 26#usize)
    (by reduce_skolem_work) (by reduce_skolem_work)
  erw [substitute_nnf]
  reduce_skolem_work
  erw [substitute_nnf_loop]
  simp [arguments, vector, alloc.vec.Vec.val, index_singleton]
  erw [substitute_term]
  reduce_skolem_work
  erw [copied]
  simp only [bind_ok, Aeneas.Std.uncurry, push_empty]
  erw [substitute_nnf_loop]
  simp [secondNnf, vector, alloc.vec.Vec.val, work]

theorem second_literal_transform :
    Transformer.transform { afterIntroduction with work := work 48#usize 26#usize }
      secondNnf skolemLimits = .ok (.Ok secondNnf, secondAfter) := by
  have copied := SkolemCopy.constant_term 0#u32
    (work 49#usize 27#usize) (work 50#usize 27#usize) (work 50#usize 28#usize)
    (by reduce_skolem_work) (by reduce_skolem_work)
  have literalCopy := SkolemCopy.literal_one true 0#u32
    (.Fun 0#u32 (vector [] (by simp))) (.Fun 0#u32 (vector [] (by simp))) skolemLimits
    (work 49#usize 27#usize) (work 50#usize 28#usize) copied
  unfold secondNnf
  erw [Transformer.transform]
  reduce_skolem_work
  erw [literalCopy]
  simp [secondAfter, vector, work, Aeneas.Std.uncurry]

theorem second_transform :
    Transformer.transform secondBefore (.Exists 0#u32 (.Literal ⟨true, 0#u32, arguments⟩)) skolemLimits =
      .ok (.Ok secondNnf, secondAfter) := by
  have tick : Work.tick secondBefore.work skolemLimits =
      .ok (.Ok (), work 44#usize 21#usize) := by
    change Work.tick (work 43#usize 21#usize) skolemLimits = _
    reduce_skolem_work
  erw [Transformer.transform]
  simp only [tick, bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry]
  erw [introduce_constant]
  simp only [bind_ok, Aeneas.Std.uncurry]
  erw [substitute_constant]
  simp only [bind_ok, Aeneas.Std.uncurry]
  exact second_literal_transform

#print axioms FangQuantifiedKernel.substitute_constant
#print axioms FangQuantifiedKernel.second_literal_transform
#print axioms FangQuantifiedKernel.second_transform
end FangQuantifiedKernel
