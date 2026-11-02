/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import QuantifiedKernelPrimitives

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel

theorem u32_usize (value : U32) : UScalar.cast .Usize value =
    UScalar.ofNatCore (ty := .Usize) value.val (by scalar_tac) := by
  apply UScalar.eq_of_val_eq
  simp

theorem core_bounded_add (left right cap : Usize)
    (kind : fang_skolem_core.fang_quantified_fof_core.Resource)
    (fits : left.val + right.val ≤ cap.val) :
    fang_skolem_core.fang_quantified_fof_core.bounded_add left right cap kind =
      .ok (.Ok (UScalar.ofNatCore (ty := .Usize) (left.val + right.val) (by scalar_tac))) := by
  rw [fang_skolem_core.fang_quantified_fof_core.bounded_add, ite_eq_right (by scalar_tac)]
  rw [sub_value cap left (by scalar_tac)]
  simp only [bind_ok]
  rw [ite_eq_right (by scalar_tac), add_value left right (by scalar_tac)]
  simp only [bind_ok]

#print axioms FangQuantifiedKernel.core_bounded_add
#print axioms FangQuantifiedKernel.u32_usize
end FangQuantifiedKernel
