/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Soundness and scope of the depth-parameterised formula parsers of `FofInputDepth`, for every bound. The
   proofs are those of `unit_formula_chain_sound` (`FofFormulaSound`) and `unit_formula_chain_within`
   (`FofScope`) with the parameterised parsers; the token grammars and `Formula.Within` carry no depth, so a
   depth test only adds failures. -/
import FofInputDepth
import FofScope

namespace Fang.TptpCandidate.FullFof
open Grammar

theorem checkedAt_exact {maxDepth depth endOffset original value rest output final}
    (success : checkedAt maxDepth depth endOffset original value rest = .ok (output, final)) :
    output = value ∧ final = rest := by
  unfold checkedAt at success
  split at success
  · simp [failure] at success
  · simpa only [Except.ok.injEq, Prod.mk.injEq, eq_comm] using success

theorem unit_formula_chain_at_sound (maxDepth fuel : Nat) :
    (∀ depth bound endOffset input value rest,
      unitAt maxDepth fuel depth bound endOffset input = .ok (value, rest) → UnitTokens input value rest) ∧
    (∀ depth bound endOffset input value rest,
      formulaAt maxDepth fuel depth bound endOffset input = .ok (value, rest) → FormulaTokens input value rest) ∧
    (∀ depth bound endOffset operator left input value rest,
      chainAt maxDepth fuel depth bound endOffset operator left input = .ok (value, rest) →
        ChainTokens operator left input value rest) := by
  induction fuel with
  | zero =>
    constructor
    · intro depth bound endOffset input value rest success
      simp [unitAt, failure] at success
    constructor
    · intro depth bound endOffset input value rest success
      simp [formulaAt, failure] at success
    · intro depth bound endOffset operator left input value rest success
      simp [chainAt, failure] at success
  | succ fuel ih =>
    constructor
    · intro depth bound endOffset input value final success
      unfold unitAt at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ _ token rest _ kind
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact .truth kind
      · rename_i _ _ token rest _ kind
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact .falsity kind
      · rename_i _ _ token rest _ kind _ result call
        obtain ⟨rfl, rfl⟩ := checkedAt_exact success
        exact .neg kind (ih.1 _ _ _ _ _ _ call)
      · rename_i _ _ token rest _ kind _ result call _ closing closeAt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        have closeShape := expect_exact closeAt
        have parsed := ih.2.1 _ _ _ _ _ _ call
        rw [closeShape.1] at parsed
        exact .group kind parsed closeShape.2
      · rename_i _ _ token rest _ kind _ opening openAt _ names namesAt _
          _ closing closeAt _ colon colonAt _ body bodyAt
        obtain ⟨rfl, rfl⟩ := checkedAt_exact success
        have openShape := expect_exact openAt
        have closeShape := expect_exact closeAt
        have colonShape := expect_exact colonAt
        have bindersParsed := binders_sound _ namesAt
        rw [closeShape.1, colonShape.1] at bindersParsed
        rw [openShape.1]
        simpa [kind] using UnitTokens.quantified (universal := true) kind openShape.2
          bindersParsed closeShape.2 colonShape.2 (ih.1 _ _ _ _ _ _ bodyAt)
      · rename_i _ _ token rest _ kind _ opening openAt _ names namesAt _
          _ closing closeAt _ colon colonAt _ body bodyAt
        obtain ⟨rfl, rfl⟩ := checkedAt_exact success
        have openShape := expect_exact openAt
        have closeShape := expect_exact closeAt
        have colonShape := expect_exact colonAt
        have bindersParsed := binders_sound _ namesAt
        rw [closeShape.1, colonShape.1] at bindersParsed
        rw [openShape.1]
        have flag : (token.kind == .legacy (.punctuation '!')) = false := by rw [kind]; decide
        simpa only [flag] using UnitTokens.quantified (universal := false) kind openShape.2
          bindersParsed closeShape.2 colonShape.2 (ih.1 _ _ _ _ _ _ bodyAt)
      · rename_i _ _ token rest _ _ _ _ _ _ _ _ _ result call
        obtain ⟨rfl, rfl⟩ := checkedAt_exact success
        exact .atom (atom_sound call)
    constructor
    · intro depth bound endOffset input value final success
      simp only [formulaAt, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ result call _ empty
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact .one (ih.1 _ _ _ _ _ _ call) (by simp [nextBinary, empty])
      · rename_i _ result call _ next tail shape _ noOperator
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact .one (ih.1 _ _ _ _ _ _ call) (by simp [nextBinary, shape, noOperator])
      · rename_i _ result call _ next tail shape _ operator operatorAt
        exact .binary (ih.1 _ _ _ _ _ _ call) (ih.2.2 _ _ _ _ _ _ _ _ success)
    · intro depth bound endOffset operator left input value final success
      unfold chainAt at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ token rest operatorAt _ right rightAt _ checkedResult checkedAt more
        have kind : binary token.kind = some operator := by simpa using operatorAt
        have continued : operator.associative = true ∧ nextBinary right.2 = some operator := by
          simpa only [nextBinary, Bool.and_eq_true, beq_iff_eq] using more
        exact .more kind (ih.1 _ _ _ _ _ _ rightAt) continued.1 continued.2
          (ih.2.2 _ _ _ _ _ _ _ _ success)
      · rename_i _ token rest operatorAt _ right rightAt _ checkedResult checkedAt finished
        have kind : binary token.kind = some operator := by simpa using operatorAt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact .one kind (ih.1 _ _ _ _ _ _ rightAt) (by simpa only [nextBinary, Bool.not_eq_true] using finished)

theorem unit_formula_chain_at_within (maxDepth fuel : Nat) :
    (∀ depth bound endOffset input value rest,
      unitAt maxDepth fuel depth bound endOffset input = .ok (value, rest) → value.Within bound) ∧
    (∀ depth bound endOffset input value rest,
      formulaAt maxDepth fuel depth bound endOffset input = .ok (value, rest) → value.Within bound) ∧
    (∀ depth bound endOffset operator left input value rest, left.Within bound →
      chainAt maxDepth fuel depth bound endOffset operator left input = .ok (value, rest) → value.Within bound) := by
  induction fuel with
  | zero =>
    constructor
    · intro depth bound endOffset input value rest success; simp [unitAt, failure] at success
    constructor
    · intro depth bound endOffset input value rest success; simp [formulaAt, failure] at success
    · intro depth bound endOffset operator left input value rest _ success
      simp [chainAt, failure] at success
  | succ fuel ih =>
    constructor
    · intro depth bound endOffset input value final success
      unfold unitAt at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success); trivial
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success); trivial
      · rename_i _ _ token rest _ kind _ result call
        obtain ⟨rfl, rfl⟩ := checkedAt_exact success
        exact (show Formula.Within bound result.1 from ih.1 _ _ _ _ _ _ call)
      · rename_i _ _ token rest _ kind _ result call _ closing closeAt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact ih.2.1 _ _ _ _ _ _ call
      · rename_i _ _ token rest _ kind _ opening openAt _ names namesAt _
          _ closing closeAt _ colon colonAt _ body bodyAt
        obtain ⟨rfl, rfl⟩ := checkedAt_exact success
        exact (close_within _ _ _ _).mpr (ih.1 _ _ _ _ _ _ bodyAt)
      · rename_i _ _ token rest _ kind _ opening openAt _ names namesAt _
          _ closing closeAt _ colon colonAt _ body bodyAt
        obtain ⟨rfl, rfl⟩ := checkedAt_exact success
        exact (close_within _ _ _ _).mpr (ih.1 _ _ _ _ _ _ bodyAt)
      · rename_i _ _ token rest _ _ _ _ _ _ _ _ _ result call
        obtain ⟨rfl, rfl⟩ := checkedAt_exact success
        exact atom_within call
    constructor
    · intro depth bound endOffset input value final success
      simp only [formulaAt, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ result call _ empty
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact ih.1 _ _ _ _ _ _ call
      · rename_i _ result call _ next tail shape _ noOperator
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact ih.1 _ _ _ _ _ _ call
      · rename_i _ result call _ next tail shape _ operator operatorAt
        exact ih.2.2 _ _ _ _ _ _ _ _ (ih.1 _ _ _ _ _ _ call) success
    · intro depth bound endOffset operator left input value final leftWithin success
      unfold chainAt at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ token rest operatorAt _ right rightAt _ checkedResult checkedAt more
        have combined : (Formula.pair operator left right.1).Within bound :=
          ⟨leftWithin, ih.1 _ _ _ _ _ _ rightAt⟩
        exact ih.2.2 _ _ _ _ _ _ _ _ combined success
      · rename_i _ token rest operatorAt _ right rightAt _ checkedResult checkedAt finished
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact ⟨leftWithin, ih.1 _ _ _ _ _ _ rightAt⟩

theorem unitAt_sound {maxDepth fuel depth bound endOffset input value rest}
    (success : unitAt maxDepth fuel depth bound endOffset input = .ok (value, rest)) :
    UnitTokens input value rest := (unit_formula_chain_at_sound maxDepth fuel).1 _ _ _ _ _ _ success

theorem formulaAt_sound {maxDepth fuel depth bound endOffset input value rest}
    (success : formulaAt maxDepth fuel depth bound endOffset input = .ok (value, rest)) :
    FormulaTokens input value rest := (unit_formula_chain_at_sound maxDepth fuel).2.1 _ _ _ _ _ _ success

theorem chainAt_sound {maxDepth fuel depth bound endOffset operator left input value rest}
    (success : chainAt maxDepth fuel depth bound endOffset operator left input = .ok (value, rest)) :
    ChainTokens operator left input value rest :=
  (unit_formula_chain_at_sound maxDepth fuel).2.2 _ _ _ _ _ _ _ _ success

theorem formulaAt_within {maxDepth fuel depth bound endOffset input value rest}
    (success : formulaAt maxDepth fuel depth bound endOffset input = .ok (value, rest)) : value.Within bound :=
  (unit_formula_chain_at_within maxDepth fuel).2.1 _ _ _ _ _ _ success

#print axioms Fang.TptpCandidate.FullFof.checkedAt_exact
#print axioms Fang.TptpCandidate.FullFof.unit_formula_chain_at_sound
#print axioms Fang.TptpCandidate.FullFof.unitAt_sound
#print axioms Fang.TptpCandidate.FullFof.formulaAt_sound
#print axioms Fang.TptpCandidate.FullFof.chainAt_sound
#print axioms Fang.TptpCandidate.FullFof.unit_formula_chain_at_within
#print axioms Fang.TptpCandidate.FullFof.formulaAt_within

end Fang.TptpCandidate.FullFof
