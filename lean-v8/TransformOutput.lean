/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft output invariants for the binder-removal boundary. Unchecked. -/
import Transform
import ProblemExtension
import BinderSyntax

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core
open fang_skolem_core.fang_quantified_fof_core (Nnf)

/-- A structural representation decoder, with no preprocessing or rewriting. -/
def decodeIndependentNnf : Nnf → Fang.QuantifiedFOF.Nnf
  | .Literal literal => .lit ⟨literal.positive, decodeAtom literal⟩
  | .True => .truth
  | .False => .falsity
  | .And left right => .conj (decodeIndependentNnf left) (decodeIndependentNnf right)
  | .Or left right => .disj (decodeIndependentNnf left) (decodeIndependentNnf right)
  | .Forall id body => .all id.val (decodeIndependentNnf body)
  | .Exists id body => .ex id.val (decodeIndependentNnf body)

theorem decodeIndependent_within (formula : Nnf) (free : List Nat) :
    (decodeIndependentNnf formula).Within free ↔ (decodeNnf formula).Within free := by
  induction formula generalizing free with
  | Literal literal =>
    cases positive : literal.positive <;>
      simp [decodeIndependentNnf, decodeNnf, literalFormula, positive,
        Fang.QuantifiedFOF.Nnf.Within, Fang.QuantifiedFOF.Formula.Within]
  | True | False => rfl
  | And left right il ir | Or left right il ir => exact and_congr (il free) (ir free)
  | Forall id body ih | Exists id body ih => exact ih (id.val :: free)

theorem decodeIndependent_binders (formula : Nnf) :
    Fang.QuantifiedFOF.BinderRemoval.binders (decodeIndependentNnf formula) =
      formulaBinders (decodeNnf formula) := by
  induction formula with
  | Literal literal =>
    cases positive : literal.positive <;>
      simp [decodeIndependentNnf, decodeNnf, literalFormula, positive,
        Fang.QuantifiedFOF.BinderRemoval.binders, formulaBinders]
  | True | False => rfl
  | And left right il ir | Or left right il ir =>
    simp only [decodeIndependentNnf, decodeNnf, Fang.QuantifiedFOF.BinderRemoval.binders,
      formulaBinders, il, ir]
  | Forall id body ih | Exists id body ih =>
    simp only [decodeIndependentNnf, decodeNnf, Fang.QuantifiedFOF.BinderRemoval.binders,
      formulaBinders, ih]

theorem decodeIndependent_holds {D : Type} (model : Fang.Interpretation D)
    (formula : Nnf) (valuation : Nat → D) :
    (decodeIndependentNnf formula).Holds model valuation ↔ (decodeNnf formula).Holds model valuation := by
  induction formula generalizing valuation with
  | Literal literal =>
    cases positive : literal.positive <;>
      simp [decodeIndependentNnf, decodeNnf, literalFormula, positive,
        Fang.QuantifiedFOF.Nnf.Holds, Fang.QuantifiedFOF.Formula.Holds, Fang.Literal.Holds]
  | True | False => rfl
  | And left right il ir => exact and_congr (il valuation) (ir valuation)
  | Or left right il ir => exact or_congr (il valuation) (ir valuation)
  | Forall id body ih => exact forall_congr' (fun value => ih _)
  | Exists id body ih => exact exists_congr (fun value => ih _)

theorem decodeIndependent_noExists (formula : Nnf) :
    Fang.QuantifiedFOF.BinderRemoval.NoExists (decodeIndependentNnf formula) ↔
      Fang.QuantifiedFOF.Skolem.existentialCount (decodeNnf formula) = 0 := by
  induction formula with
  | Literal literal => cases positive : literal.positive <;> simp [decodeIndependentNnf,
      Fang.QuantifiedFOF.BinderRemoval.NoExists, decodeNnf, literalFormula,
      positive, Fang.QuantifiedFOF.Skolem.existentialCount]
  | True | False => simp [decodeIndependentNnf, Fang.QuantifiedFOF.BinderRemoval.NoExists,
      decodeNnf, Fang.QuantifiedFOF.Skolem.existentialCount]
  | And left right il ir | Or left right il ir =>
    simpa only [decodeIndependentNnf, Fang.QuantifiedFOF.BinderRemoval.NoExists,
      decodeNnf, Fang.QuantifiedFOF.Skolem.existentialCount, Nat.add_eq_zero_iff] using and_congr il ir
  | Forall id body ih => exact ih
  | Exists id body ih => simp [decodeIndependentNnf, Fang.QuantifiedFOF.BinderRemoval.NoExists,
      decodeNnf, Fang.QuantifiedFOF.Skolem.existentialCount]

theorem variableValues_nodup (ids : List U32) : ids.Nodup → (ids.map (fun id => id.val)).Nodup := by
  induction ids with
  | nil => intro unique; simp
  | cons id rest ih =>
    intro unique
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp unique
    apply List.nodup_cons.mpr
    refine ⟨?_, ih tail⟩
    intro member
    obtain ⟨other, member, same⟩ := List.mem_map.mp member
    have equal : other = id := UScalar.eq_of_val_eq same
    exact absent (equal ▸ member)

theorem transform_output_rectified {before after : Transformer} {source target : Nnf} {limits : Limits}
    (valid : UniversalValid before.universals)
    (ready : TransformReady (universalIds before.universals) source)
    (room : TransformRoom before source)
    (success : Transformer.transform before source limits = .ok (.Ok target, after)) :
    Fang.QuantifiedFOF.BinderRemoval.RectifiedWithin (universalIds before.universals)
      (decodeIndependentNnf target) := by
  have converted := (transform_success valid ready room success).2.2.2.2
  have sublist := skolemized_binders converted
  refine ⟨(decodeIndependent_within target _).mpr (skolemized_within converted ready.1), ?_, ?_⟩
  · rw [decodeIndependent_binders]
    apply sublist.nodup
    rw [decoded_nnf_binders]
    exact variableValues_nodup _ ready.2.1
  · intro id member
    rw [decodeIndependent_binders] at member
    have sourceMember := sublist.subset member
    rw [decoded_nnf_binders] at sourceMember
    obtain ⟨original, present, same⟩ := List.mem_map.mp sourceMember
    exact same ▸ ready.2.2 original present

theorem transform_output_noExists {before after : Transformer} {source target : Nnf} {limits : Limits}
    (valid : UniversalValid before.universals)
    (ready : TransformReady (universalIds before.universals) source)
    (room : TransformRoom before source)
    (success : Transformer.transform before source limits = .ok (.Ok target, after)) :
    Fang.QuantifiedFOF.BinderRemoval.NoExists (decodeIndependentNnf target) := by
  have converted := (transform_success valid ready room success).2.2.2.2
  exact (decodeIndependent_noExists target).mpr
    (Fang.QuantifiedFOF.Skolem.skolemized_counter_exact converted).2

/-- This is the function-table length, not an arity/origin inventory theorem. -/
theorem transform_function_count {before after : Transformer} {source target : Nnf} {limits : Limits}
    (valid : UniversalValid before.universals)
    (ready : TransformReady (universalIds before.universals) source)
    (room : TransformRoom before source)
    (success : Transformer.transform before source limits = .ok (.Ok target, after)) :
    after.functions.val.length = before.functions.val.length +
      Fang.QuantifiedFOF.Skolem.existentialCount (decodeNnf source) :=
  (Fang.QuantifiedFOF.Skolem.skolemized_counter_exact
    (transform_success valid ready room success).2.2.2.2).1

end FangSkolemCore
