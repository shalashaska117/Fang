/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import FofTermSound

namespace Fang.TptpCandidate.FullFof
open Grammar
deriving instance ReflBEq, LawfulBEq for Binary

private theorem bind_ok {α β ε : Type} {result : Except ε α} {next : α → Except ε β} {value : β}
    (success : (result >>= next) = .ok value) :
    ∃ first, result = .ok first ∧ next first = .ok value := by
  cases result with
  | error reason => simp [bind, Except.bind] at success
  | ok first => exact ⟨first, rfl, success⟩

theorem checked_exact {depth endOffset original value rest output final}
    (success : checked depth endOffset original value rest = .ok (output, final)) :
    output = value ∧ final = rest := by
  unfold checked at success
  split at success
  · simp [failure] at success
  · simpa only [Except.ok.injEq, Prod.mk.injEq, eq_comm] using success

theorem binders_sound (fuel : Nat) {endOffset input names final}
    (success : binders fuel endOffset input = .ok (names, final)) :
    BindersTokens input names final := by
  induction fuel generalizing input names final with
  | zero => simp [binders, failure] at success
  | succ fuel ih =>
    simp only [binders, failure, bind, Except.bind, pure, Except.pure] at success
    repeat' first | contradiction | split at success
    · rename_i _ token rest _ name kind notTyped comma _ result tailAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      obtain ⟨separator, tail, shape, separatorKind⟩ := isChar_exact comma
      rw [shape] at tailAt ⊢
      exact .more kind separatorKind (ih (by simpa using tailAt))
    · rename_i _ token rest _ name kind notTyped notComma
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      exact .one kind (by simpa using notComma) (by simpa using notTyped)

theorem unit_formula_chain_sound (fuel : Nat) :
    (∀ depth bound endOffset input value rest,
      unit fuel depth bound endOffset input = .ok (value, rest) → UnitTokens input value rest) ∧
    (∀ depth bound endOffset input value rest,
      formula fuel depth bound endOffset input = .ok (value, rest) → FormulaTokens input value rest) ∧
    (∀ depth bound endOffset operator left input value rest,
      chain fuel depth bound endOffset operator left input = .ok (value, rest) →
        ChainTokens operator left input value rest) := by
  induction fuel with
  | zero =>
    constructor
    · intro depth bound endOffset input value rest success
      simp [unit, failure] at success
    constructor
    · intro depth bound endOffset input value rest success
      simp [formula, failure] at success
    · intro depth bound endOffset operator left input value rest success
      simp [chain, failure] at success
  | succ fuel ih =>
    constructor
    · intro depth bound endOffset input value final success
      unfold unit at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ _ token rest _ kind
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact .truth kind
      · rename_i _ _ token rest _ kind
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact .falsity kind
      · rename_i _ _ token rest _ kind _ result call
        obtain ⟨rfl, rfl⟩ := checked_exact success
        exact .neg kind (ih.1 _ _ _ _ _ _ call)
      · rename_i _ _ token rest _ kind _ result call _ closing closeAt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        have closeShape := expect_exact closeAt
        have parsed := ih.2.1 _ _ _ _ _ _ call
        rw [closeShape.1] at parsed
        exact .group kind parsed closeShape.2
      · rename_i _ _ token rest _ kind _ opening openAt _ names namesAt _
          _ closing closeAt _ colon colonAt _ body bodyAt
        obtain ⟨rfl, rfl⟩ := checked_exact success
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
        obtain ⟨rfl, rfl⟩ := checked_exact success
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
        obtain ⟨rfl, rfl⟩ := checked_exact success
        exact .atom (atom_sound call)
    constructor
    · intro depth bound endOffset input value final success
      simp only [formula, bind, Except.bind, pure, Except.pure] at success
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
      unfold chain at success
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

theorem unit_sound {fuel depth bound endOffset input value rest}
    (success : unit fuel depth bound endOffset input = .ok (value, rest)) :
    UnitTokens input value rest := (unit_formula_chain_sound fuel).1 _ _ _ _ _ _ success

theorem formula_sound {fuel depth bound endOffset input value rest}
    (success : formula fuel depth bound endOffset input = .ok (value, rest)) :
    FormulaTokens input value rest := (unit_formula_chain_sound fuel).2.1 _ _ _ _ _ _ success

theorem chain_sound {fuel depth bound endOffset operator left input value rest}
    (success : chain fuel depth bound endOffset operator left input = .ok (value, rest)) :
    ChainTokens operator left input value rest :=
  (unit_formula_chain_sound fuel).2.2 _ _ _ _ _ _ _ _ success

#print axioms Fang.TptpCandidate.FullFof.checked_exact
#print axioms Fang.TptpCandidate.FullFof.binders_sound
#print axioms Fang.TptpCandidate.FullFof.unit_formula_chain_sound
#print axioms Fang.TptpCandidate.FullFof.unit_sound
#print axioms Fang.TptpCandidate.FullFof.formula_sound
#print axioms Fang.TptpCandidate.FullFof.chain_sound

end Fang.TptpCandidate.FullFof
