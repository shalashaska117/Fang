/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Small exact-call equations for the retained one-literal clause blocks. -/
import QuantifiedRemovalKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel.Clausifier
open fang_fof_core
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def limits : Limits := {
  max_formula_depth := 64#usize, max_formula_nodes := 10000#usize,
  max_term_depth := 64#usize, max_input_term_nodes := 100000#usize,
  max_clauses := 1000#usize, max_literals_per_clause := 256#usize,
  max_literals := 100000#usize, max_stored_nodes := 1000000#usize,
  max_operations := 5000000#usize }

def work (operations stored : Usize) : Work :=
  ⟨⟨operations, 0#usize, 0#usize, stored, 0#usize, 0#usize, 0#usize⟩⟩

theorem bounded_add_value (left right cap : Usize) (kind : Resource)
    (fits : left.val + right.val ≤ cap.val) :
    bounded_add left right cap kind =
      .ok (.Ok (UScalar.ofNatCore (ty := .Usize) (left.val + right.val) (by scalar_tac))) := by
  rw [bounded_add, ite_eq_right (by scalar_tac)]
  rw [sub_value cap left (by scalar_tac)]
  simp only [bind_ok]
  rw [ite_eq_right (by scalar_tac), add_value left right (by scalar_tac)]
  simp only [bind_ok]

macro "reduce_clausifier_work" : tactic => `(tactic|
  simp (disch := scalar_tac) [FangQuantifiedKernel.Clausifier.work,
    fang_fof_core.Work.tick, fang_fof_core.Work.allocate,
    FangQuantifiedKernel.Clausifier.bounded_add_value,
    FangQuantifiedKernel.Clausifier.limits, FangOriginalKernelProbe.add_value,
    FangOriginalKernelProbe.sub_value, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, lift])

theorem copy_variable (id : U32) :
    copy_term (.Var id) limits (work 2#usize 2#usize) =
      .ok (.Ok (.Var id), work 3#usize 3#usize) := by
  rw [copy_term]
  reduce_clausifier_work

theorem copy_constant (symbol : U32) :
    copy_term (.Fun symbol (vector [] (by simp))) limits (work 2#usize 2#usize) =
      .ok (.Ok (.Fun symbol (vector [] (by simp))), work 3#usize 3#usize) := by
  rw [copy_term]
  reduce_clausifier_work
  erw [copy_term_loop]
  simp [vector, alloc.vec.Vec.val]
  rfl

def oneClause (positive : Bool) (predicate : U32) (term : fang.syntax.Term) : Preprocessed := {
  clauses := vector [vector [⟨positive, predicate, vector [term] (by simp; scalar_tac)⟩]
    (by simp; scalar_tac)] (by simp; scalar_tac)
  statistics := ⟨3#usize, 0#usize, 0#usize, 3#usize, 1#usize, 1#usize, 1#usize⟩ }

theorem literal_clausification (positive : Bool) (predicate : U32) (term : fang.syntax.Term)
    (copyRun : copy_term term limits (work 2#usize 2#usize) =
      .ok (.Ok term, work 3#usize 3#usize)) :
    nnf_entry.clausify_nnf_from
      (.Literal ⟨positive, predicate, vector [term] (by simp; scalar_tac)⟩)
      limits (work 0#usize 0#usize).statistics = .ok (.Ok (oneClause positive predicate term)) := by
  simp (disch := scalar_tac) [nnf_entry.clausify_nnf_from, work, limits, bounded_add_value,
    core.result.Result.Insts.CoreOpsTry.branch]
  erw [clausify_nnf]
  reduce_clausifier_work
  simp only [check_shape]
  simp
  reduce_clausifier_work
  simp only [copy_literal]
  reduce_clausifier_work
  simp only [copy_arguments]
  erw [copy_arguments_loop]
  simp (disch := scalar_tac) [vector, alloc.vec.Vec.val, alloc.vec.Vec.deref, Slice.index_usize]
  erw [copyRun]
  simp (disch := scalar_tac) only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, push_empty, add_value]
  erw [copy_arguments_loop]
  simp (disch := scalar_tac) [fang_fof_core.singleton, push_empty, sub_value, work,
    Aeneas.Std.uncurry,
    oneClause, vector]
  apply UScalar.eq_of_val_eq
  rfl

#print axioms FangQuantifiedKernel.Clausifier.bounded_add_value
#print axioms FangQuantifiedKernel.Clausifier.copy_variable
#print axioms FangQuantifiedKernel.Clausifier.copy_constant
#print axioms FangQuantifiedKernel.Clausifier.literal_clausification
end FangQuantifiedKernel.Clausifier
