/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Semantic transport for the relation proved of the actual Rust rectifier. -/
import EmbeddedRepresentation

namespace FangSkolemEmbeddedCore
open Aeneas.Std Aeneas.Data.ListN fang_skolem_core.fang_quantified_fof_core

theorem decodeTerms_eq_map {n : Nat} (terms : ListN fang_skolem_core.fang.syntax.Term n) :
    decodeTerms terms = terms.toList.map decodeTerm := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp [decodeTerms, ListN.toList, ih]

theorem decodeVec_eq_map (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term) :
    decodeVec arguments = arguments.val.map decodeTerm := by
  cases arguments with
  | mk slice =>
    cases slice with
    | mk count terms bound =>
      simpa [decodeVec, decodeSlice, alloc.vec.Vec.val, Slice.val] using decodeTerms_eq_map terms

theorem decodedArguments_equal {D : Type} (model : Fang.Interpretation D)
    (leftVal rightVal : Nat → D) (arguments target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
    (length : target.val.length = arguments.val.length)
    (children : ∀ i (hi : i < arguments.val.length) (ht : i < target.val.length),
      (decodeTerm arguments.val[i]).eval model leftVal = (decodeTerm target.val[i]).eval model rightVal) :
    (decodeVec arguments).map (Fang.Term.eval model leftVal) =
      (decodeVec target).map (Fang.Term.eval model rightVal) := by
  simp only [decodeVec_eq_map, List.map_map]
  apply List.ext_getElem
  · simp [length]
  · intro i hi ht
    simp only [List.getElem_map, Function.comp_apply]
    exact children i (by simpa using hi) (by simpa using ht)

def ResolverBelow (resolve : U32 → Option U32) (next : Nat) : Prop :=
  ∀ id fresh, resolve id = some fresh → fresh.val < next

def ValuationsAgree {D : Type} (resolve : U32 → Option U32)
    (sourceVal targetVal : Nat → D) : Prop :=
  ∀ id fresh, resolve id = some fresh → sourceVal id.val = targetVal fresh.val

theorem termRenaming_eval {D : Type} (model : Fang.Interpretation D)
    {resolve source target} (renamed : TermRenaming resolve source target)
    (sourceVal targetVal : Nat → D) (agrees : ValuationsAgree resolve sourceVal targetVal) :
    (decodeTerm source).eval model sourceVal = (decodeTerm target).eval model targetVal := by
  induction renamed with
  | var id fresh binding => simpa [decodeTerm, Fang.Term.eval] using agrees id fresh binding
  | fun_ symbol args target length children ih =>
    simp only [decodeTerm, Fang.Term.eval]
    congr 1
    exact decodedArguments_equal model sourceVal targetVal args target length ih

theorem shadowResolver_below {resolve first} (below : ResolverBelow resolve first)
    (id fresh : U32) (position : fresh.val = first) :
    ResolverBelow (shadowResolver resolve id fresh) (first + 1) := by
  intro queried value binding
  by_cases same : id = queried
  · simp [shadowResolver, same] at binding
    subst value
    omega
  · have old : resolve queried = some value := by simpa [shadowResolver, same] using binding
    have := below queried value old
    omega

theorem shadowResolver_agrees {D : Type} {resolve first} (below : ResolverBelow resolve first)
    (id fresh : U32) (position : fresh.val = first) (sourceVal targetVal : Nat → D)
    (agrees : ValuationsAgree resolve sourceVal targetVal) (value : D) :
    ValuationsAgree (shadowResolver resolve id fresh)
      (Fang.QuantifiedFOF.update sourceVal id.val value)
      (Fang.QuantifiedFOF.update targetVal fresh.val value) := by
  intro queried target binding
  by_cases same : id = queried
  · subst queried
    simp [shadowResolver] at binding
    subst target
    simp [Fang.QuantifiedFOF.update]
  · have old : resolve queried = some target := by simpa [shadowResolver, same] using binding
    have unequal : queried.val ≠ id.val := by
      intro equality
      apply same
      apply UScalar.eq_of_val_eq
      exact equality.symm
    have target_unequal : target.val ≠ fresh.val := by
      have := below queried target old
      omega
    simp only [Fang.QuantifiedFOF.update, ite_eq_right unequal, ite_eq_right target_unequal]
    exact agrees queried target old

/-- The range bound prevents a new target binder from capturing an outer variable. -/
theorem rectified_holds {D : Type} (model : Fang.Interpretation D)
    {resolve first source target last} (renamed : RectifiedFormula resolve first source target last)
    (below : ResolverBelow resolve first) (sourceVal targetVal : Nat → D)
    (agrees : ValuationsAgree resolve sourceVal targetVal) :
    (decodeFormula source).Holds model sourceVal ↔ (decodeFormula target).Holds model targetVal := by
  induction renamed generalizing sourceVal targetVal with
  | atom next predicate args target length children =>
    simp only [decodeFormula, Fang.QuantifiedFOF.Formula.Holds, Fang.Atom.Holds]
    rw [decodedArguments_equal model sourceVal targetVal args target length
      (fun i hi ht => termRenaming_eval model (children i hi ht) sourceVal targetVal agrees)]
  | truth next | falsity next => rfl
  | negation child ih =>
    exact not_congr (ih below sourceVal targetVal agrees)
  | @conjunction resolve first middle last sourceLeft sourceRight targetLeft targetRight left right il ir
    | @disjunction resolve first middle last sourceLeft sourceRight targetLeft targetRight left right il ir
    | @implication resolve first middle last sourceLeft sourceRight targetLeft targetRight left right il ir =>
    have belowRight : ResolverBelow resolve middle := by
      intro id fresh binding
      have bound := below id fresh binding
      have count := (rectified_counter left).1
      omega
    first
    | exact and_congr (il below sourceVal targetVal agrees) (ir belowRight sourceVal targetVal agrees)
    | exact or_congr (il below sourceVal targetVal agrees) (ir belowRight sourceVal targetVal agrees)
    | exact imp_congr (il below sourceVal targetVal agrees) (ir belowRight sourceVal targetVal agrees)
  | @universal resolve first last id fresh body target position child ih =>
    exact forall_congr' (fun value => ih (shadowResolver_below below id fresh position) _ _
      (shadowResolver_agrees below id fresh position sourceVal targetVal agrees value))
  | @existential resolve first last id fresh body target position child ih =>
    exact exists_congr (fun value => ih (shadowResolver_below below id fresh position) _ _
      (shadowResolver_agrees below id fresh position sourceVal targetVal agrees value))

end FangSkolemEmbeddedCore
