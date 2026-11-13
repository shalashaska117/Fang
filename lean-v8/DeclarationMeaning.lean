/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Original-model extension for the successful public declaration traversal. -/
import PublicDeclarations

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open Fang.QuantifiedFOF

theorem scopedTerm_below {signature : fang_quantified_fof_core.Signature} {allowed}
    {term : fang.syntax.Term} (valid : FangSkolemEmbeddedCore.ScopedTerm signature allowed term) :
    Skolem.TermBelow signature.functions.val.length (decodeTerm term) := by
  induction valid with
  | var id member => simp [decodeTerm, Skolem.TermBelow]
  | fun_ symbol arguments arity children ih =>
    simp only [decodeTerm, Skolem.TermBelow]
    refine ⟨arity.1, ?_⟩
    intro child member
    change child ∈ decodeVec arguments at member
    rw [decodeVec_eq_map] at member
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp present
    subst source
    exact ih i hi

theorem formulaValid_below (signature : fang_quantified_fof_core.Signature)
    (formula : fang_quantified_fof_core.Formula) (allowed : U32 → Prop)
    (valid : FangSkolemEmbeddedCore.FormulaValid signature allowed formula) :
    Skolem.FormulaBelow signature.functions.val.length (FangSkolemEmbeddedCore.decodeFormula formula) := by
  induction formula generalizing allowed with
  | Atom symbol arguments =>
    intro child member
    change child ∈ FangSkolemEmbeddedCore.decodeVec arguments at member
    rw [embedded_decodeVec, decodeVec_eq_map] at member
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, hi, same⟩ := List.mem_iff_getElem.mp present
    subst source
    exact scopedTerm_below (valid.2 i hi)
  | True | False => trivial
  | Not body ih => exact ih allowed valid
  | And left right il ir | Or left right il ir | Implies left right il ir =>
    exact ⟨il allowed valid.1, ir allowed valid.2⟩
  | Forall id body ih | Exists id body ih => exact ih _ valid

def NnfBelow (limit : Nat) : Nnf → Prop
  | .lit literal => ∀ term ∈ literal.atom.args, Skolem.TermBelow limit term
  | .truth | .falsity => True
  | .conj left right | .disj left right => NnfBelow limit left ∧ NnfBelow limit right
  | .all _ body | .ex _ body => NnfBelow limit body

theorem independent_nnf_below (formula : Formula) (positive : Bool) (limit : Nat)
    (below : Skolem.FormulaBelow limit formula) : NnfBelow limit (formula.nnf positive) := by
  induction formula generalizing positive with
  | atom atom => exact below
  | truth | falsity => cases positive <;> simp [Formula.nnf, NnfBelow]
  | neg body ih => exact ih _ below
  | conj left right il ir | disj left right il ir | implies left right il ir =>
    cases positive <;> exact ⟨il _ below.1, ir _ below.2⟩
  | all id body ih | ex id body ih => cases positive <;> exact ih _ below

theorem decodeNnf_below (formula : fang_quantified_fof_core.Nnf) (limit : Nat) :
    Skolem.FormulaBelow limit (decodeNnf formula) ↔ NnfBelow limit (decodeIndependentNnf formula) := by
  induction formula with
  | Literal literal =>
    cases positive : literal.positive <;>
      simp [decodeNnf, literalFormula, positive, decodeIndependentNnf, Skolem.FormulaBelow, NnfBelow]
  | True | False => rfl
  | And left right il ir | Or left right il ir => exact and_congr il ir
  | Forall id body ih | Exists id body ih => exact ih

theorem actual_normalized_below
    {declaration : Declaration} {signature : fang_quantified_fof_core.Signature}
    {coreLimits : fang_quantified_fof_core.Limits} {normalized : fang_quantified_fof_core.Normalized}
    (success : fang_quantified_fof_core.rectify_normalize_closed declaration.formula
      declaration.positive signature coreLimits = .ok (.Ok normalized)) :
    Skolem.FormulaBelow signature.functions.val.length (decodeNnf normalized.formula) := by
  have checked := FangSkolemEmbeddedCore.normalized_witness_spec declaration.formula
    declaration.positive signature coreLimits
  rw [success] at checked
  simp only [spec_ok, FangSkolemEmbeddedCore.NormalizedWitness] at checked
  obtain ⟨valid, target, count, rectified, normalizedEq⟩ := checked
  have targetValid := FangSkolemEmbeddedCore.rectified_signature rectified signature (fun _ => False) valid
  apply (decodeNnf_below _ _).mpr
  rw [← embedded_decodeNnf, normalizedEq]
  exact independent_nnf_below _ _ _ (formulaValid_below signature target _ targetValid)

def NormalizedDeclaration (signature : fang_quantified_fof_core.Signature)
    (declaration : Declaration) (formula : Formula) : Prop :=
  ∃ (normalized : fang_quantified_fof_core.Normalized) (coreLimits : fang_quantified_fof_core.Limits),
    fang_quantified_fof_core.rectify_normalize_closed declaration.formula declaration.positive
      signature coreLimits = .ok (.Ok normalized) ∧ formula = decodeNnf normalized.formula

theorem declarationTrace_factor {signature declarations first targets last}
    (trace : DeclarationTrace signature declarations first targets last) :
    ∃ sources, List.Forall₂ (NormalizedDeclaration signature) declarations sources ∧
      Skolem.ProblemSkolemized first sources (targets.map decodeNnf) last := by
  induction trace with
  | nil first => exact ⟨[], .nil, .nil first⟩
  | @cons declaration declarations first middle last target targets normalized coreLimits success head tail ih =>
    obtain ⟨sources, normalizedTail, convertedTail⟩ := ih
    exact ⟨decodeNnf normalized.formula :: sources,
      .cons ⟨normalized, coreLimits, success, rfl⟩ normalizedTail, .cons head convertedTail⟩

theorem normalizedDeclaration_holds {signature declaration formula}
    (normalization : NormalizedDeclaration signature declaration formula)
    {D : Type} (model : Fang.Interpretation D) (valuation : Nat → D) :
    formula.Holds model valuation ↔ Fang.GroundFOF.signed declaration.positive
      ((FangSkolemEmbeddedCore.decodeFormula declaration.formula).Holds model valuation) := by
  obtain ⟨normalized, coreLimits, success, rfl⟩ := normalization
  have checked := FangSkolemEmbeddedCore.rectify_normalize_closed_semantics declaration.formula
    declaration.positive signature coreLimits model valuation
  rw [success] at checked
  simp only [spec_ok] at checked
  apply (decodeIndependent_holds model normalized.formula valuation).symm.trans
  rw [← embedded_decodeNnf]
  exact checked

theorem normalizedList_holds {signature declarations formulas}
    (normalizations : List.Forall₂ (NormalizedDeclaration signature) declarations formulas)
    {D : Type} (model : Fang.Interpretation D) (valuation : Nat → D) :
    (∀ formula ∈ formulas, formula.Holds model valuation) ↔
      ∀ declaration ∈ declarations, Fang.GroundFOF.signed declaration.positive
        ((FangSkolemEmbeddedCore.decodeFormula declaration.formula).Holds model valuation) := by
  induction normalizations with
  | nil => simp
  | cons head tail ih =>
    simp only [List.forall_mem_cons]
    exact and_congr (normalizedDeclaration_holds head model valuation) ih

theorem normalizedList_below {signature declarations formulas}
    (normalizations : List.Forall₂ (NormalizedDeclaration signature) declarations formulas) :
    ∀ formula ∈ formulas, Skolem.FormulaBelow signature.functions.val.length formula := by
  induction normalizations with
  | nil => simp
  | cons head tail ih =>
    simp only [List.forall_mem_cons]
    obtain ⟨normalized, coreLimits, success, rfl⟩ := head
    exact ⟨actual_normalized_below success, ih⟩

/-- The same extension works for every valuation and every declaration. -/
theorem skolemize_problem_meaning
    {declarations : Slice Declaration} {signature : fang_quantified_fof_core.Signature}
    {limits : Limits} {output : Skolemized}
    (success : skolemize_problem declarations signature limits = .ok (.Ok output))
    {D : Type} [Nonempty D] (original : Fang.Interpretation D) :
    ∃ extended : Fang.Interpretation D,
      Skolem.PreservesBelow signature.functions.val.length original extended ∧
      ∀ valuation,
        (∀ declaration ∈ declarations.val, Fang.GroundFOF.signed declaration.positive
          ((FangSkolemEmbeddedCore.decodeFormula declaration.formula).Holds original valuation)) ↔
        ∀ formula ∈ output.formulas.val, (decodeNnf formula).Holds extended valuation := by
  obtain ⟨sources, normalized, converted⟩ := declarationTrace_factor (skolemize_problem_success success).2.2
  obtain ⟨extended, preserves, equivalent⟩ :=
    Skolem.problemSkolemized_extension converted (normalizedList_below normalized) original
  refine ⟨extended, preserves, ?_⟩
  intro valuation
  exact (normalizedList_holds normalized original valuation).symm.trans
    ((equivalent valuation).trans (by simp))

theorem normalized_skolem_output {signature normalized coreLimits first target last} {declaration : Declaration}
    (normalization : fang_quantified_fof_core.rectify_normalize_closed declaration.formula
      declaration.positive signature coreLimits = .ok (.Ok normalized))
    (converted : Skolem.Skolemized [] first (decodeNnf normalized.formula) (decodeNnf target) last) :
    BinderRemoval.RectifiedWithin [] (decodeIndependentNnf target) ∧
      BinderRemoval.NoExists (decodeIndependentNnf target) := by
  have ready := (actual_normalized_ready normalization).1
  have sublist := skolemized_binders converted
  refine ⟨⟨(decodeIndependent_within target []).mpr (skolemized_within converted ready.1), ?_, by simp⟩, ?_⟩
  · rw [decodeIndependent_binders]
    apply sublist.nodup
    rw [decoded_nnf_binders]
    exact variableValues_nodup _ ready.2.1
  · exact (decodeIndependent_noExists target).mpr (Skolem.skolemized_counter_exact converted).2

theorem declarationTrace_output {signature declarations first targets last}
    (trace : DeclarationTrace signature declarations first targets last) :
    ∀ target ∈ targets, BinderRemoval.RectifiedWithin [] (decodeIndependentNnf target) ∧
      BinderRemoval.NoExists (decodeIndependentNnf target) := by
  induction trace with
  | nil => simp
  | cons normalized coreLimits normalization converted tail ih =>
    simp only [List.forall_mem_cons]
    exact ⟨normalized_skolem_output normalization converted, ih⟩

theorem skolemize_problem_output
    {declarations : Slice Declaration} {signature : fang_quantified_fof_core.Signature}
    {limits : Limits} {output : Skolemized}
    (success : skolemize_problem declarations signature limits = .ok (.Ok output)) :
    ∀ target ∈ output.formulas.val, BinderRemoval.RectifiedWithin [] (decodeIndependentNnf target) ∧
      BinderRemoval.NoExists (decodeIndependentNnf target) :=
  declarationTrace_output (skolemize_problem_success success).2.2

theorem skolemize_problem_independent_meaning
    {declarations : Slice Declaration} {signature : fang_quantified_fof_core.Signature}
    {limits : Limits} {output : Skolemized}
    (success : skolemize_problem declarations signature limits = .ok (.Ok output))
    {D : Type} [Nonempty D] (original : Fang.Interpretation D) :
    ∃ extended : Fang.Interpretation D,
      Skolem.PreservesBelow signature.functions.val.length original extended ∧
      ∀ valuation,
        (∀ declaration ∈ declarations.val, Fang.GroundFOF.signed declaration.positive
          ((FangSkolemEmbeddedCore.decodeFormula declaration.formula).Holds original valuation)) ↔
        ∀ formula ∈ output.formulas.val, (decodeIndependentNnf formula).Holds extended valuation := by
  obtain ⟨extended, preserved, meaning⟩ := skolemize_problem_meaning success original
  refine ⟨extended, preserved, fun valuation => (meaning valuation).trans ?_⟩
  exact forall_congr' (fun formula => forall_congr' (fun _ =>
    (decodeIndependent_holds extended formula valuation).symm))

end FangSkolemCore
