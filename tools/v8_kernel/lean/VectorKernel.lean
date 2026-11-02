/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Generic exact vector equations with list-level capacity premises. -/
import QuantifiedKernelPrimitives

open Aeneas Aeneas.Std
namespace FangKernelGenerator

theorem push_from {α : Type} (values : List α) (bound : values.length ≤ Usize.max)
    (value : α) (fits : values.length < Usize.max) :
    alloc.vec.Vec.push ⟨Slice.from values bound⟩ value =
      .ok (FangQuantifiedKernel.vector (values ++ [value]) (by simp; omega)) := by
  have action := FangQuantifiedKernel.push_values
    (⟨Slice.from values bound⟩ : alloc.vec.Vec α) value
    (by simpa only [alloc.vec.Vec.val, Slice.from_val] using fits)
  simpa only [alloc.vec.Vec.val, Slice.from_val] using action

theorem index_from {α : Type} (values : List α) (bound : values.length ≤ Usize.max)
    (index : Usize) (within : index.val < values.length) :
    alloc.vec.Vec.index_usize ⟨Slice.from values bound⟩ index = .ok values[index.val] := by
  have action := FangQuantifiedKernel.index_value
    (⟨Slice.from values bound⟩ : alloc.vec.Vec α) index
    (by simpa only [alloc.vec.Vec.val, Slice.from_val] using within)
  simpa only [alloc.vec.Vec.val, Slice.from_val] using action

#print axioms FangKernelGenerator.push_from
#print axioms FangKernelGenerator.index_from
end FangKernelGenerator
