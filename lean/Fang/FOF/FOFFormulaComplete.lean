/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFLiteralComplete
import Fang.FOF.FOFWellFormed
import Fang.FOF.FOFFormulaUniqueness
import Fang.FOF.FOFFuel

namespace Fang.FOFFrontend
open Frontend FOFGrammar

def RawFormulaCompletion (signature : Source.Signature) (state : State)
    (named : NamedFOF.Formula) (rest : List String) : Prop :=
  ∃ fuel encoded updated, formula fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ spellings updated = rest ∧
    TableFormulaEncoding updated named encoded ∧ TableExtension state updated

theorem raw_formulaCompletion_of_success {signature state input named rest fuel encoded updated}
    (parsed : FormulaTokens input named rest) (words : spellings state = input)
    (success : formula fuel state = .ok (encoded, updated))
    (compatible : SignatureCompatible signature updated) :
    RawFormulaCompletion signature state named rest := by
  obtain ⟨actual, encoding, extension, grammar⟩ := raw_formula_grammar fuel success
  rw [words] at grammar
  obtain ⟨rfl, equal⟩ := parsed.unique grammar
  exact ⟨fuel, encoded, updated, success, compatible, equal.symm, encoding, extension⟩

theorem raw_formula_atom_run {name state fuel}
    (head : state.tokens.head?.map Token.text = some name)
    (valid : Source.Grammar.LowerName name) :
    formula (fuel + 1) state = (do
      let (literal, updated) ← Frontend.literal fuel state
      pure (GroundFOF.Formula.atom literal.atom, updated)) := by
  have validBool := raw_lower_valid valid
  have notTruth : name ≠ "$true" := fun same => truth_not_lower (same ▸ valid)
  have notFalsity : name ≠ "$false" := fun same => Source.Grammar.false_not_lower (same ▸ valid)
  have notNegation : name ≠ "~" := fun same => negate_not_lower (same ▸ valid)
  have notOpening : name ≠ "(" := fun same => open_not_lower (same ▸ valid)
  simp [formula, bind, StateT.bind, peek_run, head, notTruth, notFalsity, notNegation,
    notOpening, validBool, pure, StateT.pure, Except.bind, Except.pure]

theorem discard_consume_after_expect {state updated name}
    (checked : expect name state = .ok ((), updated)) :
    discard consume state = .ok (PUnit.unit, updated) := by
  obtain ⟨token, rest, shape, _, rfl⟩ := expect_success checked
  have consumed := consume_cons state token rest shape
  simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, consumed]

theorem raw_formula_complete {input named rest} (parsed : FormulaTokens input named rest)
    (signature : Source.Signature) (state : State) (words : spellings state = input)
    (wellFormed : named.WellFormed signature) (compatible : SignatureCompatible signature state) :
    RawFormulaCompletion signature state named rest := by
  induction parsed generalizing state with
  | atom atom =>
    obtain ⟨fuel, encoded, updated, success, finalCompatible, _, _, _⟩ :=
      raw_literal_complete (.positive atom) signature state words wellFormed compatible
    obtain ⟨remaining, inputShape, valid⟩ := atom.app_head
    have head := congrArg List.head? (words.trans inputShape)
    simp only [spellings_head, List.head?_cons] at head
    have formulaRun : formula (fuel + 1) state = .ok (.atom encoded.atom, updated) := by
      rw [raw_formula_atom_run head valid]
      simp [success, bind, Except.bind, pure, Except.pure]
    exact raw_formulaCompletion_of_success (.atom atom) words formulaRun finalCompatible
  | truth rest =>
    obtain ⟨updated, checked, _, _, functions, predicates⟩ := raw_expect_complete words
    have head : state.tokens.head?.map Token.text = some "$true" := by rw [← spellings_head, words]; rfl
    have success : formula 1 state = .ok (.truth, updated) := by
      simp [formula, bind, StateT.bind, peek_run, head, checked,
        pure, StateT.pure, Except.bind, Except.pure]
    exact raw_formulaCompletion_of_success (.truth rest) words success
      (compatible.same_tables functions predicates)
  | falsity rest =>
    obtain ⟨updated, checked, _, _, functions, predicates⟩ := raw_expect_complete words
    have head : state.tokens.head?.map Token.text = some "$false" := by rw [← spellings_head, words]; rfl
    have success : formula 1 state = .ok (.falsity, updated) := by
      simp [formula, bind, StateT.bind, peek_run, head, checked,
        pure, StateT.pure, Except.bind, Except.pure]
    exact raw_formulaCompletion_of_success (.falsity rest) words success
      (compatible.same_tables functions predicates)
  | neg child ih =>
    obtain ⟨opened, opening, childWords, _, functions, predicates⟩ := raw_expect_complete words
    obtain ⟨fuel, encoded, updated, childRun, finalCompatible, _, _, _⟩ :=
      ih opened childWords wellFormed (compatible.same_tables functions predicates)
    have head : state.tokens.head?.map Token.text = some "~" := by rw [← spellings_head, words]; rfl
    have success : formula (fuel + 1) state = .ok (.neg encoded, updated) := by
      simp [formula, bind, StateT.bind, peek_run, head, opening, childRun,
        pure, StateT.pure, Except.bind, Except.pure]
    exact raw_formulaCompletion_of_success (.neg child) words success finalCompatible
  | paren child ih =>
    obtain ⟨opened, opening, childWords, _, functions, predicates⟩ := raw_expect_complete words
    obtain ⟨fuel, encoded, afterChild, childRun, childCompatible, closingWords, _, _⟩ :=
      ih opened childWords wellFormed (compatible.same_tables functions predicates)
    obtain ⟨updated, closing, _, _, finalFunctions, finalPredicates⟩ := raw_expect_complete closingWords
    have head : state.tokens.head?.map Token.text = some "(" := by rw [← spellings_head, words]; rfl
    have childHead : afterChild.tokens.head?.map Token.text = some ")" := by
      rw [← spellings_head, closingWords]; rfl
    have success : formula (fuel + 1) state = .ok (encoded, updated) := by
      simp [formula, bind, StateT.bind, peek_run, head, opening, childRun, childHead, closing,
        pure, StateT.pure, Except.bind, Except.pure]
    exact raw_formulaCompletion_of_success (.paren child) words success
      (childCompatible.same_tables finalFunctions finalPredicates)
  | conj first second ih₁ ih₂ =>
    obtain ⟨opened, opening, firstWords, _, functions, predicates⟩ := raw_expect_complete words
    obtain ⟨firstFuel, left, afterLeft, leftRun, leftCompatible, operatorWords, _, _⟩ :=
      ih₁ opened firstWords wellFormed.1 (compatible.same_tables functions predicates)
    obtain ⟨afterOperator, operatorRun, rightWords, _, nextFunctions, nextPredicates⟩ := raw_expect_complete operatorWords
    obtain ⟨rightFuel, right, afterRight, rightRun, rightCompatible, closingWords, _, _⟩ :=
      ih₂ afterOperator rightWords wellFormed.2 (leftCompatible.same_tables nextFunctions nextPredicates)
    obtain ⟨updated, closing, _, _, finalFunctions, finalPredicates⟩ := raw_expect_complete closingWords
    let fuel := max firstFuel rightFuel
    have leftRun' := formula_fuel_monotone firstFuel fuel (Nat.le_max_left _ _) opened left afterLeft leftRun
    have rightRun' := formula_fuel_monotone rightFuel fuel (Nat.le_max_right _ _) afterOperator right afterRight rightRun
    have head : state.tokens.head?.map Token.text = some "(" := by rw [← spellings_head, words]; rfl
    have operatorHead : afterLeft.tokens.head?.map Token.text = some "&" := by
      rw [← spellings_head, operatorWords]; rfl
    have consumed := discard_consume_after_expect operatorRun
    have success : formula (fuel + 1) state = .ok (.conj left right, updated) := by
      simp [formula, bind, StateT.bind, peek_run, head, opening, leftRun', operatorHead,
        consumed, rightRun', closing, pure, StateT.pure, Except.bind, Except.pure]
    exact raw_formulaCompletion_of_success (.conj first second) words success
      (rightCompatible.same_tables finalFunctions finalPredicates)
  | disj first second ih₁ ih₂ =>
    obtain ⟨opened, opening, firstWords, _, functions, predicates⟩ := raw_expect_complete words
    obtain ⟨firstFuel, left, afterLeft, leftRun, leftCompatible, operatorWords, _, _⟩ :=
      ih₁ opened firstWords wellFormed.1 (compatible.same_tables functions predicates)
    obtain ⟨afterOperator, operatorRun, rightWords, _, nextFunctions, nextPredicates⟩ := raw_expect_complete operatorWords
    obtain ⟨rightFuel, right, afterRight, rightRun, rightCompatible, closingWords, _, _⟩ :=
      ih₂ afterOperator rightWords wellFormed.2 (leftCompatible.same_tables nextFunctions nextPredicates)
    obtain ⟨updated, closing, _, _, finalFunctions, finalPredicates⟩ := raw_expect_complete closingWords
    let fuel := max firstFuel rightFuel
    have leftRun' := formula_fuel_monotone firstFuel fuel (Nat.le_max_left _ _) opened left afterLeft leftRun
    have rightRun' := formula_fuel_monotone rightFuel fuel (Nat.le_max_right _ _) afterOperator right afterRight rightRun
    have head : state.tokens.head?.map Token.text = some "(" := by rw [← spellings_head, words]; rfl
    have operatorHead : afterLeft.tokens.head?.map Token.text = some "|" := by
      rw [← spellings_head, operatorWords]; rfl
    have consumed := discard_consume_after_expect operatorRun
    have success : formula (fuel + 1) state = .ok (.disj left right, updated) := by
      simp [formula, bind, StateT.bind, peek_run, head, opening, leftRun', operatorHead,
        consumed, rightRun', closing, pure, StateT.pure, Except.bind, Except.pure]
    exact raw_formulaCompletion_of_success (.disj first second) words success
      (rightCompatible.same_tables finalFunctions finalPredicates)
  | implies first second ih₁ ih₂ =>
    obtain ⟨opened, opening, firstWords, _, functions, predicates⟩ := raw_expect_complete words
    obtain ⟨firstFuel, left, afterLeft, leftRun, leftCompatible, operatorWords, _, _⟩ :=
      ih₁ opened firstWords wellFormed.1 (compatible.same_tables functions predicates)
    obtain ⟨afterOperator, operatorRun, rightWords, _, nextFunctions, nextPredicates⟩ := raw_expect_complete operatorWords
    obtain ⟨rightFuel, right, afterRight, rightRun, rightCompatible, closingWords, _, _⟩ :=
      ih₂ afterOperator rightWords wellFormed.2 (leftCompatible.same_tables nextFunctions nextPredicates)
    obtain ⟨updated, closing, _, _, finalFunctions, finalPredicates⟩ := raw_expect_complete closingWords
    let fuel := max firstFuel rightFuel
    have leftRun' := formula_fuel_monotone firstFuel fuel (Nat.le_max_left _ _) opened left afterLeft leftRun
    have rightRun' := formula_fuel_monotone rightFuel fuel (Nat.le_max_right _ _) afterOperator right afterRight rightRun
    have head : state.tokens.head?.map Token.text = some "(" := by rw [← spellings_head, words]; rfl
    have operatorHead : afterLeft.tokens.head?.map Token.text = some "=>" := by
      rw [← spellings_head, operatorWords]; rfl
    have consumed := discard_consume_after_expect operatorRun
    have success : formula (fuel + 1) state = .ok (.implies left right, updated) := by
      simp [formula, bind, StateT.bind, peek_run, head, opening, leftRun', operatorHead,
        consumed, rightRun', closing, pure, StateT.pure, Except.bind, Except.pure]
    exact raw_formulaCompletion_of_success (.implies first second) words success
      (rightCompatible.same_tables finalFunctions finalPredicates)

end Fang.FOFFrontend
