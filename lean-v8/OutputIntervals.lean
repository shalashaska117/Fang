/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Proof witnesses for original binder intervals, including deleted/unused IDs. -/
import DeclarationMeaning

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open Fang.QuantifiedFOF

/-- This ignores binder nesting and bounds every variable occurrence. It is a
    mathematical predicate; List.range is not executed by the Rust pipeline. -/
def FlatVariables (count : Nat) : Formula → Prop
  | .atom atom => ∀ term ∈ atom.args, TermWithin (List.range count) term
  | .truth | .falsity => True
  | .neg body | .all _ body | .ex _ body => FlatVariables count body
  | .conj left right | .disj left right | .implies left right =>
      FlatVariables count left ∧ FlatVariables count right

theorem flatVariables_of_within (formula : Formula) (scope : List Nat) (count : Nat)
    (within : formula.Within scope) (outer : ∀ id ∈ scope, id < count)
    (binders : ∀ id ∈ formulaBinders formula, id < count) : FlatVariables count formula := by
  induction formula generalizing scope with
  | atom atom =>
    intro term member
    exact termWithin_weaken (fun id present => List.mem_range.mpr (outer id present))
      term (within term member)
  | truth | falsity => trivial
  | neg body ih => exact ih scope within outer binders
  | conj left right il ir | disj left right il ir | implies left right il ir =>
    exact ⟨il scope within.1 outer (fun id member => binders id (List.mem_append_left _ member)),
      ir scope within.2 outer (fun id member => binders id (List.mem_append_right _ member))⟩
  | all id body ih | ex id body ih =>
    apply ih (id :: scope) within
    · intro other member
      rcases List.mem_cons.mp member with same | member
      · have below := binders id List.mem_cons_self
        omega
      · exact outer other member
    · intro other member
      exact binders other (List.mem_cons_of_mem _ member)

theorem actual_normalized_interval
    {declaration : Declaration} {signature : fang_quantified_fof_core.Signature}
    {coreLimits : fang_quantified_fof_core.Limits} {normalized : fang_quantified_fof_core.Normalized}
    (success : fang_quantified_fof_core.rectify_normalize_closed declaration.formula
      declaration.positive signature coreLimits = .ok (.Ok normalized)) :
    ∃ count : U32, (nnfBinders normalized.formula).length = count.val ∧
      ∀ id ∈ formulaBinders (decodeNnf normalized.formula), id < count.val := by
  have checked := FangSkolemEmbeddedCore.normalized_witness_spec declaration.formula
    declaration.positive signature coreLimits
  rw [success] at checked
  simp only [spec_ok, FangSkolemEmbeddedCore.NormalizedWitness] at checked
  obtain ⟨_, target, count, renamed, normalizedEq⟩ := checked
  refine ⟨count, (normalized_ready renamed normalizedEq).2, ?_⟩
  intro id member
  rw [← decodeIndependent_binders, ← embedded_decodeNnf, normalizedEq,
    independent_nnf_binders, embedded_formula_binders] at member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (FangSkolemEmbeddedCore.rectified_binder_interval renamed present).2

theorem normalized_skolem_interval
    {declaration : Declaration} {signature : fang_quantified_fof_core.Signature}
    {coreLimits : fang_quantified_fof_core.Limits} {normalized : fang_quantified_fof_core.Normalized}
    {first last : Nat} {target : fang_quantified_fof_core.Nnf}
    (success : fang_quantified_fof_core.rectify_normalize_closed declaration.formula
      declaration.positive signature coreLimits = .ok (.Ok normalized))
    (converted : Skolem.Skolemized [] first (decodeNnf normalized.formula) (decodeNnf target) last) :
    ∃ count : U32, (nnfBinders normalized.formula).length = count.val ∧
      FlatVariables count.val (decodeNnf target) ∧
      ∀ id ∈ formulaBinders (decodeNnf target), id < count.val := by
  obtain ⟨count, exactCount, sourceBounds⟩ := actual_normalized_interval success
  have targetBounds : ∀ id ∈ formulaBinders (decodeNnf target), id < count.val :=
    fun id member => sourceBounds id ((skolemized_binders converted).subset member)
  refine ⟨count, exactCount, ?_, targetBounds⟩
  exact flatVariables_of_within _ [] _ (skolemized_within converted (actual_normalized_ready success).1.1)
    (by simp) targetBounds

theorem declarationTrace_intervals {signature declarations first targets last}
    (trace : DeclarationTrace signature declarations first targets last) :
    ∀ target ∈ targets, ∃ count : U32, FlatVariables count.val (decodeNnf target) ∧
      ∀ id ∈ formulaBinders (decodeNnf target), id < count.val := by
  induction trace with
  | nil => simp
  | cons normalized coreLimits normalization converted tail ih =>
    simp only [List.forall_mem_cons]
    obtain ⟨count, _, flat, bound⟩ := normalized_skolem_interval normalization converted
    exact ⟨⟨count, flat, bound⟩, ih⟩

theorem skolemize_problem_intervals
    {declarations : Slice Declaration} {signature : fang_quantified_fof_core.Signature}
    {limits : Limits} {output : Skolemized}
    (success : skolemize_problem declarations signature limits = .ok (.Ok output)) :
    ∀ target ∈ output.formulas.val, ∃ count : U32, FlatVariables count.val (decodeNnf target) ∧
      ∀ id ∈ formulaBinders (decodeNnf target), id < count.val :=
  declarationTrace_intervals (skolemize_problem_success success).2.2

end FangSkolemCore
