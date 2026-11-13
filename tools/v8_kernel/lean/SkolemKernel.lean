/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact kernel equation for the extracted Skolem function. -/
import Skolem
open Aeneas Aeneas.Std
namespace FangOriginalKernelProbe
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def skolemLimits : fang_skolem_core.Limits := {
  core := {
    max_formula_depth := 64#usize, max_formula_nodes := 10000#usize,
    max_term_depth := 64#usize, max_input_term_nodes := 100000#usize,
    max_clauses := 1000#usize, max_literals_per_clause := 256#usize,
    max_literals := 100000#usize, max_stored_nodes := 1000000#usize,
    max_operations := 5000000#usize, max_binders := 10000#usize },
  max_declarations := 1000#usize, max_functions := 100000#usize, max_skolem_symbols := 10000#usize }

def declarations : Slice fang_skolem_core.Declaration :=
  Slice.from [⟨.False, true⟩] (by simp; scalar_tac)
def signature : fang_skolem_core.fang_quantified_fof_core.Signature :=
  ⟨⟨Slice.from [] (by simp)⟩, ⟨Slice.from [] (by simp)⟩⟩

theorem eq_of_exact_spec {α : Type} {action : Result α} {value : α}
    (specification : action ⦃ fun result => result = value ⦄) : action = .ok value := by
  cases observed : action.match with
  | ok result =>
    have same := Result.match.isOk.mp observed
    rw [same] at specification
    have valueEq := (WP.spec_ok _).mp specification
    exact same.trans (congrArg Result.ok valueEq)
  | vis effect next =>
    rw [Result.match.isVis.mp observed] at specification
    exact False.elim ((WP.spec_vis _ _).mp specification)
  | div =>
    rw [Result.match.isDiv.mp observed] at specification
    exact False.elim (WP.spec_div.mp specification)

theorem add_value (left right : Usize) (fits : left.val + right.val ≤ Usize.max) :
    left + right = Result.ok (UScalar.ofNatCore (ty := .Usize)
      (left.val + right.val) (by scalar_tac)) := by
  apply eq_of_exact_spec
  apply WP.spec_mono (Usize.add_spec fits)
  intro result equal
  apply UScalar.eq_of_val_eq
  simpa using equal

theorem sub_value (left right : Usize) (fits : right.val ≤ left.val) :
    left - right = Result.ok (UScalar.ofNatCore (ty := .Usize)
      (left.val - right.val) (by scalar_tac)) := by
  apply eq_of_exact_spec
  apply WP.spec_mono (Usize.sub_spec fits)
  intro result equal
  apply UScalar.eq_of_val_eq
  simp only [UScalar.ofNatCore_val_eq]
  scalar_tac

theorem default_value : core.default.DefaultUsize.default = 0#usize := rfl

@[simp, scalar_tac_simps] theorem zero_bits_val : (⟨0⟩ : Usize).val = 0 := rfl

theorem core_statistics_eq :
    fang_skolem_core.fang_quantified_fof_core.Statistics.Insts.CoreDefaultDefault.default =
      Result.ok ⟨0#usize, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize⟩ := rfl

theorem push_empty {α : Type} (value : α) :
    alloc.vec.Vec.push (alloc.vec.Vec.new α) value =
      .ok ⟨Slice.from [value] (by simp; scalar_tac)⟩ := by
  apply eq_of_exact_spec
  apply WP.spec_mono (alloc.vec.Vec.push_spec (alloc.vec.Vec.new α) value (by simp; scalar_tac))
  intro result values
  apply alloc.vec.Vec.ext
  simpa [alloc.vec.Vec.new, alloc.vec.Vec.val, alloc.vec.Vec.from] using values

macro "reduce_primitives" : tactic => `(tactic|
  simp (disch := scalar_tac) [fang_skolem_core.Work.tick, fang_skolem_core.Work.remaining,
    fang_skolem_core.Work.absorb, fang_skolem_core.Work.allocate, fang_skolem_core.bounded_add,
    fang_skolem_core.fang_quantified_fof_core.Work.tick,
    fang_skolem_core.fang_quantified_fof_core.Work.allocate,
    fang_skolem_core.fang_quantified_fof_core.bounded_add,
    fang_skolem_core.fang_quantified_fof_core.Work.new,
    fang_skolem_core.fang_quantified_fof_core.Bindings.new,
    fang_skolem_core.fang_quantified_fof_core.rectify_normalize_closed,
    fang_skolem_core.fang_quantified_fof_core.rectify_closed,
    FangOriginalKernelProbe.add_value, FangOriginalKernelProbe.sub_value,
    FangOriginalKernelProbe.default_value, FangOriginalKernelProbe.core_statistics_eq,
    alloc.vec.Vec.val, Slice.index_usize, core.result.Result.Insts.CoreOpsTry.branch,
    Aeneas.Std.uncurry, lift])

def transformed : fang_skolem_core.Skolemized := {
  formulas := ⟨Slice.from [.False] (by simp; scalar_tac)⟩
  signature := signature
  introduced := alloc.vec.Vec.new _
  statistics := ⟨7#usize, 4#usize⟩ }

theorem skolem_eq : fang_skolem_core.skolemize_problem declarations signature skolemLimits =
    .ok (.Ok transformed) := by
  simp only [declarations, signature, skolemLimits, fang_skolem_core.skolemize_problem, lift,
    fang_skolem_core.Statistics.Insts.CoreDefaultDefault.default,
    fang_skolem_core.validate_declarations, default_value]
  simp [alloc.vec.Vec.val]
  rw [fang_skolem_core.validate_declarations_loop]
  simp (disch := scalar_tac) [fang_skolem_core.Work.tick, fang_skolem_core.bounded_add,
    add_value, sub_value,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry,
    Slice.index_usize, fang_skolem_core.Work.remaining,
    fang_skolem_core.fang_quantified_fof_core.validate,
    fang_skolem_core.fang_quantified_fof_core.validate_with_scope,
    fang_skolem_core.fang_quantified_fof_core.Work.new,
    core_statistics_eq,
    fang_skolem_core.fang_quantified_fof_core.Bindings.new]
  rw [fang_skolem_core.fang_quantified_fof_core.validate_formula]
  simp (disch := scalar_tac) [fang_skolem_core.fang_quantified_fof_core.Work.tick,
    fang_skolem_core.fang_quantified_fof_core.bounded_add,
    add_value, sub_value,
    core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.uncurry, lift]
  simp (disch := scalar_tac) [fang_skolem_core.Work.absorb, fang_skolem_core.Work.allocate,
    fang_skolem_core.bounded_add, add_value, sub_value,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [fang_skolem_core.validate_declarations_loop]
  simp [fang_skolem_core.copy_arities, fang_skolem_core.copy_arities_loop,
    alloc.vec.Vec.deref, alloc.vec.Vec.val, Aeneas.Std.uncurry]
  rw [fang_skolem_core.transform_declarations, fang_skolem_core.transform_declarations_loop]
  reduce_primitives
  rw [fang_skolem_core.fang_quantified_fof_core.validate_formula]
  reduce_primitives
  rw [fang_skolem_core.fang_quantified_fof_core.rectify_formula]
  reduce_primitives
  rw [fang_skolem_core.fang_quantified_fof_core.normalize_formula]
  reduce_primitives
  rw [fang_skolem_core.Transformer.transform]
  reduce_primitives
  simp only [push_empty, bind_ok]
  rw [fang_skolem_core.transform_declarations_loop]
  simp [Aeneas.Std.uncurry,
    transformed, signature, alloc.vec.Vec.from, alloc.vec.Vec.new]


#print axioms FangOriginalKernelProbe.eq_of_exact_spec
#print axioms FangOriginalKernelProbe.add_value
#print axioms FangOriginalKernelProbe.sub_value
#print axioms FangOriginalKernelProbe.default_value
#print axioms FangOriginalKernelProbe.zero_bits_val
#print axioms FangOriginalKernelProbe.core_statistics_eq
#print axioms FangOriginalKernelProbe.push_empty
#print axioms FangOriginalKernelProbe.skolem_eq
end FangOriginalKernelProbe
