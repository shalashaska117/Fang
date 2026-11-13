/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   A checked construction relation; no claim about an executable Rust transformer. -/
import SymbolBounds

namespace Fang.QuantifiedFOF.Skolem

/-- The counter is global across the traversal. Existing symbols are reserved
    below the initial counter. Each existential uses all enclosing universal IDs
    in order and has explicit scope/capture obligations after earlier substitutions. -/
inductive Skolemized : List Nat → Nat → Formula → Formula → Nat → Prop where
  | atom (universals first atom) : Skolemized universals first (.atom atom) (.atom atom) first
  | truth (universals first) : Skolemized universals first .truth .truth first
  | falsity (universals first) : Skolemized universals first .falsity .falsity first
  | negation {universals first last source target}
      (child : Skolemized universals first source target last) :
      Skolemized universals first (.neg source) (.neg target) last
  | conjunction {universals first middle last left right l r}
      (leftChild : Skolemized universals first left l middle)
      (rightChild : Skolemized universals middle right r last) :
      Skolemized universals first (.conj left right) (.conj l r) last
  | disjunction {universals first middle last left right l r}
      (leftChild : Skolemized universals first left l middle)
      (rightChild : Skolemized universals middle right r last) :
      Skolemized universals first (.disj left right) (.disj l r) last
  | implication {universals first middle last left right l r}
      (leftChild : Skolemized universals first left l middle)
      (rightChild : Skolemized universals middle right r last) :
      Skolemized universals first (.implies left right) (.implies l r) last
  | universal {universals first last id body target}
      (child : Skolemized (universals ++ [id]) first body target last) :
      Skolemized universals first (.all id body) (.all id target) last
  | existential {universals first last id body target}
      (within : body.Within (id :: universals))
      (safe : CaptureSafe id (.app first (universals.map Term.var)) body)
      (child : Skolemized universals (first + 1)
        (substitute id (.app first (universals.map Term.var)) body) target last) :
      Skolemized universals first (.ex id body) target last

theorem skolemized_counter {universals first source target last}
    (converted : Skolemized universals first source target last) : first ≤ last := by
  induction converted with
  | atom | truth | falsity => omega
  | negation child ih | universal child ih => exact ih
  | conjunction l r il ir | disjunction l r il ir | implication l r il ir => omega
  | existential within safe child ih => omega

theorem skolemized_below {universals first source target last}
    (converted : Skolemized universals first source target last)
    (reserved : FormulaBelow first source) : FormulaBelow last target := by
  induction converted with
  | atom | truth | falsity => exact reserved
  | negation child ih | universal child ih => exact ih reserved
  | conjunction left right il ir | disjunction left right il ir | implication left right il ir =>
    simp only [FormulaBelow] at reserved ⊢
    exact ⟨formulaBelow_mono (skolemized_counter right) _ (il reserved.1),
      ir (formulaBelow_mono (skolemized_counter left) _ reserved.2)⟩
  | @existential universals first last id body target within safe child ih =>
    exact ih (substitution_below (first + 1) id _ body (skolem_term_below first universals)
      (formulaBelow_mono (by omega) body reserved))

/-- A single model extension works for every valuation, so quantified parents
    and sibling branches compose without choosing a different function per use. -/
theorem skolemized_extension {D : Type} [Nonempty D]
    {universals first source target last} (converted : Skolemized universals first source target last)
    (reserved : FormulaBelow first source) (original : Interpretation D) :
    ∃ extended : Interpretation D, PreservesBelow first original extended ∧
      ∀ valuation, source.Holds original valuation ↔ target.Holds extended valuation := by
  induction converted generalizing original with
  | atom | truth | falsity => exact ⟨original, ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩, fun _ => Iff.rfl⟩
  | negation child ih =>
    obtain ⟨extended, preserves, equivalent⟩ := ih reserved original
    exact ⟨extended, preserves, fun valuation => not_congr (equivalent valuation)⟩
  | @universal universals first last id body target child ih =>
    obtain ⟨extended, preserves, equivalent⟩ := ih reserved original
    exact ⟨extended, preserves, fun valuation => forall_congr' (fun value => equivalent (update valuation id value))⟩
  | @conjunction universals first middle last left right l r leftChild rightChild il ir
    | @disjunction universals first middle last left right l r leftChild rightChild il ir
    | @implication universals first middle last left right l r leftChild rightChild il ir =>
    simp only [FormulaBelow] at reserved
    obtain ⟨intermediate, preserveLeft, leftEquivalent⟩ := il reserved.1 original
    obtain ⟨extended, preserveRight, rightEquivalent⟩ := ir
      (formulaBelow_mono (skolemized_counter leftChild) right reserved.2) intermediate
    refine ⟨extended, preservesBelow_trans preserveLeft
      (preservesBelow_mono (skolemized_counter leftChild) preserveRight), ?_⟩
    intro valuation
    have lEquivalent := (leftEquivalent valuation).trans
      (formula_holds_preserved preserveRight l (skolemized_below leftChild reserved.1) valuation).symm
    have rEquivalent := (formula_holds_preserved preserveLeft right reserved.2 valuation).symm.trans
      (rightEquivalent valuation)
    first
    | exact and_congr lEquivalent rEquivalent
    | exact or_congr lEquivalent rEquivalent
    | exact imp_congr lEquivalent rEquivalent
  | @existential universals first last id body target within safe child ih =>
    obtain ⟨intermediate, preserves, equivalent⟩ := existential_extension original first universals id body reserved within safe
    obtain ⟨extended, preservesNext, nextEquivalent⟩ := ih
      (substitution_below (first + 1) id _ body (skolem_term_below first universals)
        (formulaBelow_mono (by omega) body reserved)) intermediate
    exact ⟨extended, preservesBelow_trans preserves (preservesBelow_mono (by omega) preservesNext),
      fun valuation => (equivalent valuation).trans (nextEquivalent valuation)⟩

end Fang.QuantifiedFOF.Skolem
