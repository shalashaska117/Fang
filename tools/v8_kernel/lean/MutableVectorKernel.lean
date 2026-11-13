/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import VectorKernel

open Aeneas Aeneas.Std
namespace FangKernelGenerator

theorem index_mut_value {α : Type} (values : alloc.vec.Vec α) (index : Usize)
    (inside : index.val < values.val.length) :
    values.index_mut_usize index = .ok (values.val[index.val], values.set index) := by
  apply FangOriginalKernelProbe.eq_of_exact_spec
  apply WP.spec_mono (alloc.vec.Vec.index_mut_usize_spec values index inside)
  intro output equal
  exact Prod.ext equal.1 equal.2

theorem usize_u32 (value : Usize) (fits : value.val ≤ U32.max) :
    UScalar.cast .U32 value = UScalar.ofNatCore (ty := .U32) value.val (by scalar_tac) := by
  apply UScalar.eq_of_val_eq
  simp only [UScalar.cast_val_eq, UScalar.ofNatCore_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

#print axioms FangKernelGenerator.index_mut_value
#print axioms FangKernelGenerator.usize_u32
end FangKernelGenerator
