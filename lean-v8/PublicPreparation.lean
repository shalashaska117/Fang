/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft representation/scope bridge for the public Skolem call. Unchecked. -/
import EmbeddedRectifyNormalize
import TransformOutput

namespace FangSkolemCore
open Aeneas.Std Aeneas.Data.ListN fang_skolem_core

mutual
theorem embedded_decodeTerm (term : fang.syntax.Term) :
    FangSkolemEmbeddedCore.decodeTerm term = decodeTerm term := by
  cases term with
  | Var id => rfl
  | Fun symbol arguments =>
    simp only [FangSkolemEmbeddedCore.decodeTerm, decodeTerm, embedded_decodeVec arguments]
theorem embedded_decodeVec (arguments : alloc.vec.Vec fang.syntax.Term) :
    FangSkolemEmbeddedCore.decodeVec arguments = decodeVec arguments := by
  cases arguments with
  | mk slice => exact embedded_decodeSlice slice
theorem embedded_decodeSlice (slice : Slice fang.syntax.Term) :
    FangSkolemEmbeddedCore.decodeSlice slice = decodeSlice slice := by
  cases slice with
  | mk count terms bound => exact embedded_decodeTerms terms
theorem embedded_decodeTerms {n : Nat} (terms : ListN fang.syntax.Term n) :
    FangSkolemEmbeddedCore.decodeTerms terms = decodeTerms terms := by
  cases terms with
  | nil => rfl
  | cons term rest =>
    simp only [FangSkolemEmbeddedCore.decodeTerms, decodeTerms,
      embedded_decodeTerm term, embedded_decodeTerms rest]
end

theorem embedded_decodeNnf (formula : fang_quantified_fof_core.Nnf) :
    FangSkolemEmbeddedCore.decodeNnf formula = decodeIndependentNnf formula := by
  induction formula with
  | Literal literal =>
    simp only [FangSkolemEmbeddedCore.decodeNnf, FangSkolemEmbeddedCore.decodeLiteral,
      decodeIndependentNnf, decodeAtom, embedded_decodeVec]
  | True | False => rfl
  | And left right il ir | Or left right il ir =>
    simp only [FangSkolemEmbeddedCore.decodeNnf, decodeIndependentNnf, il, ir]
  | Forall id body ih | Exists id body ih =>
    simp only [FangSkolemEmbeddedCore.decodeNnf, decodeIndependentNnf, ih]

end FangSkolemCore

namespace FangSkolemEmbeddedCore
open Aeneas.Std fang_skolem_core.fang_quantified_fof_core

/-- Every output variable is the image of a resolver binding. This premise
    does not impose a global bijection on the original source IDs. -/
theorem termRenaming_within {resolve source target} (renamed : TermRenaming resolve source target)
    (free : List Nat) (covered : ∀ id fresh, resolve id = some fresh → fresh.val ∈ free) :
    Fang.QuantifiedFOF.TermWithin free (decodeTerm target) := by
  induction renamed with
  | var id fresh binding =>
    simpa only [decodeTerm, Fang.QuantifiedFOF.TermWithin] using covered id fresh binding
  | fun_ symbol arguments target length children ih =>
    simp only [decodeTerm, Fang.QuantifiedFOF.TermWithin, decodeVec_eq_map]
    intro child member
    obtain ⟨term, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp sourceMember
    exact ih i (by omega) hi

theorem rectified_within {resolve first source target last}
    (renamed : RectifiedFormula resolve first source target last)
    (free : List Nat) (covered : ∀ id fresh, resolve id = some fresh → fresh.val ∈ free) :
    (decodeFormula target).Within free := by
  induction renamed generalizing free with
  | atom next predicate arguments target length children =>
    simp only [decodeFormula, Fang.QuantifiedFOF.Formula.Within, decodeVec_eq_map]
    intro child member
    obtain ⟨term, sourceMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp sourceMember
    exact termRenaming_within (children i (by omega) hi) free covered
  | truth | falsity => trivial
  | negation child ih => exact ih free covered
  | conjunction left right il ir | disjunction left right il ir | implication left right il ir =>
    exact ⟨il free covered, ir free covered⟩
  | @universal resolve first last id fresh body target position child ih
    | @existential resolve first last id fresh body target position child ih =>
    apply ih (fresh.val :: free)
    intro queried value binding
    by_cases same : id = queried
    · simp [shadowResolver, same] at binding
      subst value
      exact List.mem_cons_self
    · have original : resolve queried = some value := by simpa [shadowResolver, same] using binding
      exact List.mem_cons_of_mem _ (covered queried value original)

theorem rectified_closed {source target count}
    (renamed : RectifiedFormula (fun _ => none) 0 source target count) :
    (decodeFormula target).Within [] :=
  rectified_within renamed [] (by intro id fresh impossible; cases impossible)

end FangSkolemEmbeddedCore

namespace FangSkolemCore
open fang_skolem_core

theorem independent_nnf_binders (formula : Fang.QuantifiedFOF.Formula) (positive : Bool) :
    Fang.QuantifiedFOF.BinderRemoval.binders (formula.nnf positive) = formulaBinders formula := by
  induction formula generalizing positive with
  | atom atom => rfl
  | truth | falsity => cases positive <;> rfl
  | neg body ih => exact ih (!positive)
  | conj left right il ir | disj left right il ir | implies left right il ir =>
    cases positive <;> simp [Fang.QuantifiedFOF.Formula.nnf,
      Fang.QuantifiedFOF.BinderRemoval.binders, formulaBinders, il, ir]
  | all id body ih | ex id body ih =>
    cases positive <;> simp [Fang.QuantifiedFOF.Formula.nnf,
      Fang.QuantifiedFOF.BinderRemoval.binders, formulaBinders, ih]

theorem embedded_formula_binders (formula : fang_quantified_fof_core.Formula) :
    formulaBinders (FangSkolemEmbeddedCore.decodeFormula formula) =
      (FangSkolemEmbeddedCore.binderIds formula).map (fun id => id.val) := by
  induction formula with
  | Atom | True | False => rfl
  | Not body ih => exact ih
  | And left right il ir | Or left right il ir | Implies left right il ir =>
    simp only [FangSkolemEmbeddedCore.decodeFormula, formulaBinders,
      FangSkolemEmbeddedCore.binderIds, List.map_append, il, ir]
  | Forall id body ih | Exists id body ih =>
    simp only [FangSkolemEmbeddedCore.decodeFormula, formulaBinders,
      FangSkolemEmbeddedCore.binderIds, List.map_cons, ih]

end FangSkolemCore
