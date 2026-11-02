/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact introduction of the captured nullary Skolem symbol. -/
import UniversalTransformKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
open fang_skolem_core
open SkolemWork
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def secondBefore : Transformer := {
  firstAfter with
  declaration := 1#usize
  work := work 43#usize 21#usize }

def freshConstant : fang.syntax.Term := .Fun 0#u32 (alloc.vec.Vec.new _)

def afterIntroduction : Transformer := {
  secondBefore with
  functions := vector [0#usize] (by simp; scalar_tac)
  introduced := vector [⟨1#usize, 0#u32, 0#u32, alloc.vec.Vec.new _⟩] (by simp; scalar_tac)
  work := work 45#usize 24#usize }

theorem cast_zero : UScalar.cast .U32 (0#usize) = 0#u32 := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  simp

theorem function_cap : core.cmp.impls.OrdUsize.min skolemLimits.max_functions
    (UScalar.cast .Usize core.num.U32.MAX) = 100000#usize := by
  simp [skolemLimits, u32_usize, core.num.U32.MAX, U32.rMax, core.cmp.impls.OrdUsize.min]

theorem introduce_constant :
    Transformer.introduce { secondBefore with work := work 44#usize 21#usize } 0#u32 skolemLimits =
      .ok (.Ok freshConstant, afterIntroduction) := by
  unfold Transformer.introduce
  reduce_skolem_work
  simp only [secondBefore, firstAfter, firstBefore]
  simp [alloc.vec.Vec.val, alloc.vec.Vec.new, alloc.vec.Vec.from]
  simp only [copy_dependencies]
  erw [copy_dependencies_loop]
  simp only [vector]
  simp
  simp only [push_empty_slice, bind_ok]
  simp [afterIntroduction, secondBefore, firstAfter, firstBefore, freshConstant,
    vector, work, U32.rMax]
  erw [cast_zero]
  exact ⟨rfl, rfl⟩

#print axioms FangQuantifiedKernel.cast_zero
#print axioms FangQuantifiedKernel.function_cap
#print axioms FangQuantifiedKernel.introduce_constant
end FangQuantifiedKernel
