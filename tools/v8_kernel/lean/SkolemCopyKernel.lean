/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact one-element copy equations for the actual Skolem traversal. -/
import SkolemWorkKernel

open Aeneas Aeneas.Std
open FangOriginalKernelProbe
namespace FangQuantifiedKernel
namespace SkolemCopy
open fang_skolem_core
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem variable_term (id : U32) (before ticked after : Work)
    (tick : Work.tick before skolemLimits = .ok (.Ok (), ticked))
    (allocate : Work.allocate ticked 1#usize skolemLimits = .ok (.Ok (), after)) :
    copy_term (.Var id) 1#usize skolemLimits before = .ok (.Ok (.Var id), after) := by
  rw [copy_term]
  have depth : core.cmp.impls.OrdUsize.min skolemLimits.core.max_term_depth 64#usize = 64#usize := by cbv
  simp [tick, allocate, depth,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift]

theorem constant_term (id : U32) (before ticked after : Work)
    (tick : Work.tick before skolemLimits = .ok (.Ok (), ticked))
    (allocate : Work.allocate ticked 1#usize skolemLimits = .ok (.Ok (), after)) :
    copy_term (.Fun id (vector [] (by simp))) 1#usize skolemLimits before =
      .ok (.Ok (.Fun id (vector [] (by simp))), after) := by
  rw [copy_term]
  have depth : core.cmp.impls.OrdUsize.min skolemLimits.core.max_term_depth 64#usize = 64#usize := by cbv
  simp [tick, allocate, depth,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift]
  erw [copy_term_loop]
  simp [vector, alloc.vec.Vec.val]
  rfl

theorem literal_one (positive : Bool) (predicate : U32) (term copied : fang.syntax.Term)
    (limits : Limits) (before after : Work)
    (copy : copy_term term 1#usize limits before = .ok (.Ok copied, after)) :
    copy_literal ⟨positive, predicate, vector [term] (by simp; scalar_tac)⟩ limits before =
      .ok (.Ok ⟨positive, predicate, vector [copied] (by simp; scalar_tac)⟩, after) := by
  simp only [copy_literal]
  rw [copy_literal_loop]
  simp [vector, alloc.vec.Vec.val, index_singleton]
  erw [copy]
  simp (disch := scalar_tac) only [bind_ok, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, push_empty, add_value]
  rw [copy_literal_loop]
  simp [alloc.vec.Vec.val]

theorem arities_empty (limits : Limits) (before : Work) :
    copy_arities (Slice.from [] (by simp)) limits before =
      .ok (.Ok (alloc.vec.Vec.new _), before) := by
  simp [copy_arities, copy_arities_loop]

theorem arities_singleton (arity : Usize) (limits : Limits) (before ticked after : Work)
    (tick : Work.tick before limits = .ok (.Ok (), ticked))
    (allocate : Work.allocate ticked 1#usize limits = .ok (.Ok (), after)) :
    copy_arities (Slice.from [arity] (by simp; scalar_tac)) limits before =
      .ok (.Ok (vector [arity] (by simp; scalar_tac)), after) := by
  simp only [copy_arities]
  rw [copy_arities_loop]
  simp (disch := scalar_tac) [tick, allocate, Slice.index_usize, push_empty, add_value,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry]
  rw [copy_arities_loop]
  simp [vector]

#print axioms FangQuantifiedKernel.SkolemCopy.variable_term
#print axioms FangQuantifiedKernel.SkolemCopy.constant_term
#print axioms FangQuantifiedKernel.SkolemCopy.literal_one
#print axioms FangQuantifiedKernel.SkolemCopy.arities_empty
#print axioms FangQuantifiedKernel.SkolemCopy.arities_singleton
end SkolemCopy
end FangQuantifiedKernel
