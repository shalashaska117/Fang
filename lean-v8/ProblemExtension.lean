/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RecursiveExtension

namespace Fang.QuantifiedFOF.Skolem

def existentialCount : Formula → Nat
  | .atom _ | .truth | .falsity => 0
  | .neg body | .all _ body => existentialCount body
  | .conj left right | .disj left right | .implies left right =>
      existentialCount left + existentialCount right
  | .ex _ body => 1 + existentialCount body

theorem substitution_existentialCount (binder : Nat) (replacement : Term) (formula : Formula) :
    existentialCount (substitute binder replacement formula) = existentialCount formula := by
  induction formula with
  | atom | truth | falsity => rfl
  | neg body ih => exact ih
  | conj l r il ir | disj l r il ir | implies l r il ir =>
    simp only [substitute, existentialCount, il, ir]
  | all id body ih | ex id body ih =>
    by_cases same : id = binder <;> simp [substitute, same, existentialCount, ih]

theorem skolemized_counter_exact {universals first source target last}
    (converted : Skolemized universals first source target last) :
    last = first + existentialCount source ∧ existentialCount target = 0 := by
  induction converted with
  | atom | truth | falsity => simp [existentialCount]
  | negation child ih | universal child ih => exact ih
  | conjunction left right il ir | disjunction left right il ir | implication left right il ir =>
    simp only [existentialCount]
    constructor <;> omega
  | existential within safe child ih =>
    simp only [substitution_existentialCount] at ih
    simp only [existentialCount]
    constructor <;> omega

/-- The initial counter reserves the complete input signature; declarations do
    not reset this counter. Variable scopes still reset for each declaration. -/
inductive ProblemSkolemized : Nat → List Formula → List Formula → Nat → Prop where
  | nil (first : Nat) : ProblemSkolemized first [] [] first
  | cons {first middle last source target sources targets}
      (head : Skolemized [] first source target middle)
      (tail : ProblemSkolemized middle sources targets last) :
      ProblemSkolemized first (source :: sources) (target :: targets) last

theorem problemSkolemized_counter {first sources targets last}
    (converted : ProblemSkolemized first sources targets last) : first ≤ last := by
  induction converted with
  | nil => omega
  | cons head tail ih => have := skolemized_counter head; omega

theorem problemSkolemized_below {first sources targets last}
    (converted : ProblemSkolemized first sources targets last)
    (reserved : ∀ formula ∈ sources, FormulaBelow first formula) :
    ∀ formula ∈ targets, FormulaBelow last formula := by
  induction converted with
  | nil => simp
  | @cons first middle last source target sources targets head tail ih =>
    intro formula member
    rcases List.mem_cons.mp member with same | rest
    · subst formula
      exact formulaBelow_mono (problemSkolemized_counter tail) target
        (skolemized_below head (reserved source List.mem_cons_self))
    · exact ih (fun f hf => formulaBelow_mono (skolemized_counter head) f
        (reserved f (List.mem_cons_of_mem _ hf))) formula rest

/-- One extended interpretation satisfies the complete transformed input whenever
    the original interpretation satisfies the original input. The stronger
    valuation-level equivalence refers only to this constructed extension. -/
theorem problemSkolemized_extension {D : Type} [Nonempty D] {first sources targets last}
    (converted : ProblemSkolemized first sources targets last)
    (reserved : ∀ formula ∈ sources, FormulaBelow first formula) (original : Interpretation D) :
    ∃ extended : Interpretation D, PreservesBelow first original extended ∧
      ∀ valuation, (∀ formula ∈ sources, formula.Holds original valuation) ↔
        ∀ formula ∈ targets, formula.Holds extended valuation := by
  induction converted generalizing original with
  | nil => exact ⟨original, ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩, fun _ => Iff.rfl⟩
  | @cons first middle last source target sources targets head tail ih =>
    have sourceBound := reserved source List.mem_cons_self
    obtain ⟨intermediate, preservesHead, headEquivalent⟩ := skolemized_extension head sourceBound original
    obtain ⟨extended, preservesTail, tailEquivalent⟩ := ih
      (fun f hf => formulaBelow_mono (skolemized_counter head) f
        (reserved f (List.mem_cons_of_mem _ hf))) intermediate
    refine ⟨extended, preservesBelow_trans preservesHead
      (preservesBelow_mono (skolemized_counter head) preservesTail), ?_⟩
    intro valuation
    simp only [List.forall_mem_cons]
    apply and_congr
    · exact (headEquivalent valuation).trans
        (formula_holds_preserved preservesTail target (skolemized_below head sourceBound) valuation).symm
    · have originalTail : (∀ f ∈ sources, f.Holds original valuation) ↔
          ∀ f ∈ sources, f.Holds intermediate valuation := by
        apply forall_congr'
        intro f
        apply forall_congr'
        intro member
        exact (formula_holds_preserved preservesHead f
          (reserved f (List.mem_cons_of_mem _ member)) valuation).symm
      exact originalTail.trans (tailEquivalent valuation)

end Fang.QuantifiedFOF.Skolem
