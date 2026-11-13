/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   One simp traversal for a generated Boolean clausifier call. Each simproc below unfolds a
   closed application (no free, meta or loose bound variables) of one clausifier function by
   its unfold equation and hands the result back to simp, so a single traversal evaluates the
   whole call tree. No generated definition is replaced, and Lean checks the resulting proof
   term. A goal that remains goes to the step loop of BooleanClausifierPrimitives. -/
import BooleanClausifierPrimitives

open Aeneas Aeneas.Std
open Lean Meta Elab Tactic
namespace FangBooleanClausifierSinglePass

def closedUnfold (e : Expr) : SimpM Simp.Step := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .continue
  let some declaration := e.getAppFn.constName? | return .continue
  let some equation ← getUnfoldEqnFor? declaration | do
    let reduced ← deltaExpand e (· == declaration)
    if reduced == e then return .continue
    return .visit { expr := reduced }
  let some result ← withReducible <| Simp.tryTheorem? e {
      origin := .decl equation, proof := mkConst equation,
      rfl := (← isRflTheorem equation), backwardRfl := (← isBackwardRflTheorem equation) }
    | return .continue
  match ← reduceMatcher? result.expr with
  | .reduced reduced => return .visit { result with expr := reduced }
  | _ => return .visit result

simproc_decl unfold_copy_term (fang_fof_core.copy_term _ _ _) := closedUnfold
simproc_decl unfold_copy_term_loop (fang_fof_core.copy_term_loop _ _ _ _ _ _) := closedUnfold
simproc_decl unfold_copy_arguments (fang_fof_core.copy_arguments _ _ _) := closedUnfold
simproc_decl unfold_copy_arguments_loop (fang_fof_core.copy_arguments_loop _ _ _ _ _) := closedUnfold
simproc_decl unfold_copy_literal (fang_fof_core.copy_literal _ _ _) := closedUnfold
simproc_decl unfold_append_literals_loop (fang_fof_core.append_literals_loop _ _ _ _ _) := closedUnfold
simproc_decl unfold_append_literals (fang_fof_core.append_literals _ _ _ _) := closedUnfold
simproc_decl unfold_append_clauses_loop (fang_fof_core.append_clauses_loop _ _ _ _ _) := closedUnfold
simproc_decl unfold_append_clauses (fang_fof_core.append_clauses _ _ _ _) := closedUnfold
simproc_decl unfold_append_cnf (fang_fof_core.append_cnf _ _ _ _) := closedUnfold
simproc_decl unfold_product_row_loop (fang_fof_core.product_row_loop _ _ _ _ _ _) := closedUnfold
simproc_decl unfold_product_row (fang_fof_core.product_row _ _ _ _ _) := closedUnfold
simproc_decl unfold_product_cnf_loop (fang_fof_core.product_cnf_loop _ _ _ _ _ _ _ _ _) := closedUnfold
simproc_decl unfold_product_cnf (fang_fof_core.product_cnf _ _ _ _) := closedUnfold
simproc_decl unfold_clausify_nnf (fang_fof_core.clausify_nnf _ _ _) := closedUnfold
simproc_decl unfold_nnf_entry_clausify_nnf_from (fang_fof_core.nnf_entry.clausify_nnf_from _ _ _) := closedUnfold

macro "generated_boolean_clausifier_single" : tactic => `(tactic|
  ((try simp (config := { maxSteps := 5000000 }) (disch := kernel_scalar) only [
    FangKernelGenerator.index_from, FangKernelGenerator.push_from, FangKernelGenerator.usize_checked_add_value, FangKernelGenerator.usize_checked_mul_value, FangOriginalKernelProbe.add_value, FangOriginalKernelProbe.sub_value, FangOriginalReplay.initialStatistics, FangQuantifiedKernel.Clausifier.bounded_add_value, FangQuantifiedKernel.Clausifier.limits, FangQuantifiedKernel.vector, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero, List.length_cons, List.length_nil, List.nil_append, Nat.add_one_sub_one, Nat.not_ofNat_le_one, Nat.not_ofNat_lt_one, Nat.reduceAdd, Nat.reduceLT, Nat.reduceMul, Nat.reduceSub, Order.lt_one_iff, Order.lt_two_iff, Result.ok.injEq, Slice.from_val, Slice.getElem?_Usize_eq, Slice.index_usize, Slice.val_from, Std.bind_assoc, Std.le_refl, UScalar.lt_equiv, UScalar.ofNatCore_val_eq, UScalar.val_not_eq_imp_not_eq, Usize.ofNatCore_val_eq, add_zero, alloc.vec.Vec.deref, alloc.vec.Vec.from, alloc.vec.Vec.index_slice_index, alloc.vec.Vec.len, alloc.vec.Vec.val, and_self, and_true, bind_ok, core.cmp.impls.OrdUsize.max, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Ok.injEq, fang_fof_core.Preprocessed.mk.injEq, fang_fof_core.Statistics.mk.injEq, fang_fof_core.Work.allocate, fang_fof_core.Work.tick, fang_fof_core.add, fang_fof_core.check_shape, fang_fof_core.check_storage, fang_fof_core.multiply, fang_fof_core.singleton, getElem?_pos, gt_iff_lt, lift, lt_self_iff_false, mul_one, one_ne_zero, true_and, tsub_self, uncurry, zero_add, zero_le, zero_mul, ↓reduceIte, FangBooleanClausifierSinglePass.unfold_copy_term, FangBooleanClausifierSinglePass.unfold_copy_term_loop, FangBooleanClausifierSinglePass.unfold_copy_arguments, FangBooleanClausifierSinglePass.unfold_copy_arguments_loop, FangBooleanClausifierSinglePass.unfold_copy_literal, FangBooleanClausifierSinglePass.unfold_append_literals_loop, FangBooleanClausifierSinglePass.unfold_append_literals, FangBooleanClausifierSinglePass.unfold_append_clauses_loop, FangBooleanClausifierSinglePass.unfold_append_clauses, FangBooleanClausifierSinglePass.unfold_append_cnf, FangBooleanClausifierSinglePass.unfold_product_row_loop, FangBooleanClausifierSinglePass.unfold_product_row, FangBooleanClausifierSinglePass.unfold_product_cnf_loop, FangBooleanClausifierSinglePass.unfold_product_cnf, FangBooleanClausifierSinglePass.unfold_clausify_nnf, FangBooleanClausifierSinglePass.unfold_nnf_entry_clausify_nnf_from])
   <;> generated_boolean_clausifier))

end FangBooleanClausifierSinglePass
