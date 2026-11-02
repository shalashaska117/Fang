/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact equations derived from the pinned backend's total specifications. -/
import SkolemKernel

open Aeneas Aeneas.Std
namespace FangQuantifiedKernel
open FangOriginalKernelProbe

def vector {α : Type} (values : List α) (fits : values.length ≤ Usize.max) : alloc.vec.Vec α :=
  ⟨Slice.from values fits⟩

theorem push_values {α : Type} (before : alloc.vec.Vec α) (value : α)
    (fits : before.val.length < Usize.max) :
    alloc.vec.Vec.push before value =
      .ok (vector (before.val ++ [value]) (by simp; omega)) := by
  apply eq_of_exact_spec
  apply WP.spec_mono (alloc.vec.Vec.push_spec before value fits)
  intro result values
  apply alloc.vec.Vec.ext
  simpa [vector, alloc.vec.Vec.val, alloc.vec.Vec.from] using values

theorem index_value {α : Type} (before : alloc.vec.Vec α) (index : Usize)
    (within : index.val < before.val.length) :
    alloc.vec.Vec.index_usize before index = .ok before.val[index.val] := by
  apply eq_of_exact_spec
  exact alloc.vec.Vec.index_usize_spec before index within

theorem push_empty_slice {α : Type} (value : α) (bound : ([] : List α).length ≤ Usize.max) :
    alloc.vec.Vec.push ⟨Slice.from [] bound⟩ value =
      .ok (vector [value] (by simp; scalar_tac)) := by
  apply push_values
  change 0 < Usize.max
  scalar_tac

theorem index_singleton {α : Type} (value : α) (bound : [value].length ≤ Usize.max) :
    alloc.vec.Vec.index_usize ⟨Slice.from [value] bound⟩ 0#usize = .ok value := by
  exact index_value _ _ (by simp [alloc.vec.Vec.val])

theorem u32_add_value (left right : U32) (fits : left.val + right.val ≤ U32.max) :
    left + right = Result.ok (UScalar.ofNatCore (ty := .U32)
      (left.val + right.val) (by scalar_tac)) := by
  apply eq_of_exact_spec
  apply WP.spec_mono (U32.add_spec fits)
  intro result equal
  apply UScalar.eq_of_val_eq
  simpa using equal

#print axioms FangQuantifiedKernel.push_values
#print axioms FangQuantifiedKernel.index_value
#print axioms FangQuantifiedKernel.push_empty_slice
#print axioms FangQuantifiedKernel.index_singleton
#print axioms FangQuantifiedKernel.u32_add_value
end FangQuantifiedKernel
