/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Step-counted evaluation. `evalSteps` is `evalFormula` with one step per formula node visited and the same
   short-circuiting, so the steps it uses are the work it actually does; it gives up with `none` when the steps run out.
   A sentence is decided on the rewritten formula of `ModelRewrite` under every assignment of its free variables, and
   `sentenceSteps_iff` states the result for the original formula. This replaces the static estimate of
   `ModelSemantics.workOf` as the checker's work bound. This module imports no extracted code. -/
import ModelRewrite

namespace Fang.TptpCandidate.FullFof.Model

open NamedQuantified (update)

/-- A conjunction over a list with the steps threaded through. -/
def allSteps {α : Type} (test : α → Nat → Option (Bool × Nat)) : List α → Nat → Option (Bool × Nat)
  | [], fuel => some (true, fuel)
  | value :: rest, fuel =>
    match test value fuel with
    | none => none
    | some (false, left) => some (false, left)
    | some (true, left) => allSteps test rest left

/-- A disjunction over a list with the steps threaded through. -/
def anySteps {α : Type} (test : α → Nat → Option (Bool × Nat)) : List α → Nat → Option (Bool × Nat)
  | [], fuel => some (false, fuel)
  | value :: rest, fuel =>
    match test value fuel with
    | none => none
    | some (true, left) => some (true, left)
    | some (false, left) => anySteps test rest left

/-- `evalFormula` with one step per node; the value and the steps left. -/
def evalSteps (model : FiniteModel) : Formula → (String → model.Element) → Nat → Option (Bool × Nat)
  | _, _, 0 => none
  | .atom name arguments, valuation, fuel + 1 =>
    some (model.predicate name (arguments.map (Source.Term.eval model.interpretation valuation)), fuel)
  | .equal left right, valuation, fuel + 1 =>
    some (decide (left.eval model.interpretation valuation = right.eval model.interpretation valuation), fuel)
  | .truth, _, fuel + 1 => some (true, fuel)
  | .falsity, _, fuel + 1 => some (false, fuel)
  | .neg body, valuation, fuel + 1 =>
    match evalSteps model body valuation fuel with
    | none => none
    | some (value, left) => some (!value, left)
  | .pair .conj first second, valuation, fuel + 1 =>
    match evalSteps model first valuation fuel with
    | none => none
    | some (false, left) => some (false, left)
    | some (true, left) => evalSteps model second valuation left
  | .pair .disj first second, valuation, fuel + 1 =>
    match evalSteps model first valuation fuel with
    | none => none
    | some (true, left) => some (true, left)
    | some (false, left) => evalSteps model second valuation left
  | .pair .implies first second, valuation, fuel + 1 =>
    match evalSteps model first valuation fuel with
    | none => none
    | some (false, left) => some (true, left)
    | some (true, left) => evalSteps model second valuation left
  | .pair .reverse first second, valuation, fuel + 1 =>
    match evalSteps model second valuation fuel with
    | none => none
    | some (false, left) => some (true, left)
    | some (true, left) => evalSteps model first valuation left
  | .pair .nand first second, valuation, fuel + 1 =>
    match evalSteps model first valuation fuel with
    | none => none
    | some (false, left) => some (true, left)
    | some (true, left) =>
      match evalSteps model second valuation left with
      | none => none
      | some (value, rest) => some (!value, rest)
  | .pair .nor first second, valuation, fuel + 1 =>
    match evalSteps model first valuation fuel with
    | none => none
    | some (true, left) => some (false, left)
    | some (false, left) =>
      match evalSteps model second valuation left with
      | none => none
      | some (value, rest) => some (!value, rest)
  | .pair .iff first second, valuation, fuel + 1 =>
    match evalSteps model first valuation fuel with
    | none => none
    | some (one, left) =>
      match evalSteps model second valuation left with
      | none => none
      | some (other, rest) => some (one == other, rest)
  | .pair .xor first second, valuation, fuel + 1 =>
    match evalSteps model first valuation fuel with
    | none => none
    | some (one, left) =>
      match evalSteps model second valuation left with
      | none => none
      | some (other, rest) => some (one != other, rest)
  | .all name body, valuation, fuel + 1 =>
    allSteps (fun value left => evalSteps model body (update valuation name value) left)
      (List.finRange (model.size + 1)) fuel
  | .ex name body, valuation, fuel + 1 =>
    anySteps (fun value left => evalSteps model body (update valuation name value) left)
      (List.finRange (model.size + 1)) fuel

theorem allSteps_value {α : Type} {test : α → Nat → Option (Bool × Nat)} {spec : α → Bool}
    (sound : ∀ value fuel result rest, test value fuel = some (result, rest) → result = spec value) :
    ∀ (values : List α) (fuel : Nat) (result : Bool) (rest : Nat),
      allSteps test values fuel = some (result, rest) → result = values.all spec := by
  intro values
  induction values with
  | nil =>
    intro fuel result rest done
    simp only [allSteps, Option.some.injEq, Prod.mk.injEq] at done
    simp [← done.1]
  | cons value others ih =>
    intro fuel result rest done
    simp only [allSteps] at done
    cases found : test value fuel with
    | none => simp [found] at done
    | some pair =>
      obtain ⟨first, left⟩ := pair
      have head := sound value fuel first left found
      cases first with
      | false =>
        simp only [found, Option.some.injEq, Prod.mk.injEq] at done
        simp [← done.1, ← head]
      | true =>
        simp only [found] at done
        simp [← head, ih left result rest done]

theorem anySteps_value {α : Type} {test : α → Nat → Option (Bool × Nat)} {spec : α → Bool}
    (sound : ∀ value fuel result rest, test value fuel = some (result, rest) → result = spec value) :
    ∀ (values : List α) (fuel : Nat) (result : Bool) (rest : Nat),
      anySteps test values fuel = some (result, rest) → result = values.any spec := by
  intro values
  induction values with
  | nil =>
    intro fuel result rest done
    simp only [anySteps, Option.some.injEq, Prod.mk.injEq] at done
    simp [← done.1]
  | cons value others ih =>
    intro fuel result rest done
    simp only [anySteps] at done
    cases found : test value fuel with
    | none => simp [found] at done
    | some pair =>
      obtain ⟨first, left⟩ := pair
      have head := sound value fuel first left found
      cases first with
      | true =>
        simp only [found, Option.some.injEq, Prod.mk.injEq] at done
        simp [← done.1, ← head]
      | false =>
        simp only [found] at done
        simp [← head, ih left result rest done]

/-- A finished step-counted evaluation gives the value of `evalFormula`. -/
theorem evalSteps_value (model : FiniteModel) (formula : Formula) :
    ∀ (valuation : String → model.Element) (fuel : Nat) (result : Bool) (rest : Nat),
      evalSteps model formula valuation fuel = some (result, rest) → result = evalFormula model valuation formula := by
  induction formula with
  | atom name arguments =>
    intro valuation fuel result rest done
    cases fuel with
    | zero => simp [evalSteps] at done
    | succ fuel =>
      simp only [evalSteps, Option.some.injEq, Prod.mk.injEq] at done
      simp [evalFormula, ← done.1]
  | equal left right =>
    intro valuation fuel result rest done
    cases fuel with
    | zero => simp [evalSteps] at done
    | succ fuel =>
      simp only [evalSteps, Option.some.injEq, Prod.mk.injEq] at done
      simp [evalFormula, ← done.1]
  | truth =>
    intro valuation fuel result rest done
    cases fuel with
    | zero => simp [evalSteps] at done
    | succ fuel =>
      simp only [evalSteps, Option.some.injEq, Prod.mk.injEq] at done
      simp [evalFormula, ← done.1]
  | falsity =>
    intro valuation fuel result rest done
    cases fuel with
    | zero => simp [evalSteps] at done
    | succ fuel =>
      simp only [evalSteps, Option.some.injEq, Prod.mk.injEq] at done
      simp [evalFormula, ← done.1]
  | neg body ih =>
    intro valuation fuel result rest done
    cases fuel with
    | zero => simp [evalSteps] at done
    | succ fuel =>
      simp only [evalSteps] at done
      cases found : evalSteps model body valuation fuel with
      | none => simp [found] at done
      | some pair =>
        obtain ⟨value, left⟩ := pair
        simp only [found, Option.some.injEq, Prod.mk.injEq] at done
        simp [evalFormula, ← done.1, ih valuation fuel value left found]
  | pair operator first second ihFirst ihSecond =>
    intro valuation fuel result rest done
    cases fuel with
    | zero => simp [evalSteps] at done
    | succ fuel =>
      cases operator with
      | conj | disj | implies | nand | nor | iff | xor =>
        simp only [evalSteps] at done
        cases found : evalSteps model first valuation fuel with
        | none => simp [found] at done
        | some pair =>
          obtain ⟨one, left⟩ := pair
          have head := ihFirst valuation fuel one left found
          cases one <;> simp only [found] at done <;>
            first
            | (simp only [Option.some.injEq, Prod.mk.injEq] at done; simp [evalFormula, ← head, ← done.1])
            | (have tail := ihSecond valuation left result rest done; simp [evalFormula, ← head, ← tail])
            | (cases again : evalSteps model second valuation left with
               | none => simp [again] at done
               | some other =>
                 obtain ⟨two, final⟩ := other
                 have tail := ihSecond valuation left two final again
                 simp only [again, Option.some.injEq, Prod.mk.injEq] at done
                 simp [evalFormula, ← head, ← tail, ← done.1])
      | reverse =>
        simp only [evalSteps] at done
        cases found : evalSteps model second valuation fuel with
        | none => simp [found] at done
        | some pair =>
          obtain ⟨one, left⟩ := pair
          have head := ihSecond valuation fuel one left found
          cases one with
          | false =>
            simp only [found, Option.some.injEq, Prod.mk.injEq] at done
            simp [evalFormula, ← head, ← done.1]
          | true =>
            simp only [found] at done
            have tail := ihFirst valuation left result rest done
            simp [evalFormula, ← head, ← tail]
  | all name body ih =>
    intro valuation fuel result rest done
    cases fuel with
    | zero => simp [evalSteps] at done
    | succ fuel =>
      simp only [evalSteps] at done
      simp only [evalFormula]
      exact allSteps_value (fun value fuel result rest found => ih _ fuel result rest found) _ fuel result rest done
  | ex name body ih =>
    intro valuation fuel result rest done
    cases fuel with
    | zero => simp [evalSteps] at done
    | succ fuel =>
      simp only [evalSteps] at done
      simp only [evalFormula]
      exact anySteps_value (fun value fuel result rest found => ih _ fuel result rest found) _ fuel result rest done

/-- Every assignment of the listed variables, with the steps threaded through. -/
def assignSteps (model : FiniteModel) (formula : Formula) :
    List String → (String → model.Element) → Nat → Option (Bool × Nat)
  | [], valuation, fuel => evalSteps model formula valuation fuel
  | name :: rest, valuation, fuel =>
    allSteps (fun value left => assignSteps model formula rest (update valuation name value) left)
      (List.finRange (model.size + 1)) fuel

theorem assignSteps_value (model : FiniteModel) (formula : Formula) :
    ∀ (names : List String) (valuation : String → model.Element) (fuel : Nat) (result : Bool) (rest : Nat),
      assignSteps model formula names valuation fuel = some (result, rest) →
        result = evalAll model (fun valuation => evalFormula model valuation formula) names valuation := by
  intro names
  induction names with
  | nil =>
    intro valuation fuel result rest done
    exact evalSteps_value model formula valuation fuel result rest done
  | cons name others ih =>
    intro valuation fuel result rest done
    simp only [assignSteps] at done
    simp only [evalAll]
    exact allSteps_value (fun value fuel result rest found => ih _ fuel result rest found) _ fuel result rest done

/-! Sentences and statement lists. -/

inductive Decided where
  /-- The truth value of the sentence, and the steps left. -/
  | value : Bool → Nat → Decided
  /-- The computed variable list did not cover the formula; a checker fault, never a result. -/
  | scope
  /-- The steps ran out. -/
  | work

/-- Decide `∀ valuation, formula.Holds` on the rewritten formula, within `fuel` steps. -/
def sentenceSteps (model : FiniteModel) (formula : Formula) (fuel : Nat) : Decided :=
  if formulaWithin (freeVariables formula) formula then
    match assignSteps model (rewrite formula) (freeVariables formula) (fun _ => model.element 0) fuel with
    | some (result, rest) => .value result rest
    | none => .work
  else .scope

theorem sentenceSteps_iff {model : FiniteModel} {formula : Formula} {fuel : Nat} {result : Bool} {rest : Nat}
    (decided : sentenceSteps model formula fuel = .value result rest) :
    result = true ↔ ∀ valuation, formula.Holds model.interpretation valuation := by
  unfold sentenceSteps at decided
  split at decided
  · rename_i covered
    have within := (formulaWithin_iff _ formula).mp covered
    cases found : assignSteps model (rewrite formula) (freeVariables formula) (fun _ => model.element 0) fuel with
    | none => simp [found] at decided
    | some pair =>
      obtain ⟨value, left⟩ := pair
      simp only [found, Decided.value.injEq] at decided
      obtain ⟨rfl, rfl⟩ := decided
      have same := assignSteps_value model (rewrite formula) _ _ fuel value left found
      subst same
      constructor
      · intro accepted valuation
        classical
        let base : String → model.Element := fun _ => model.element 0
        let joined : String → model.Element := fun name =>
          if name ∈ freeVariables formula then valuation name else base name
        have passes := evalAll_sound model (freeVariables formula) base accepted joined (by
          intro name absent
          simp only [joined, absent, ↓reduceIte])
        have holds := (rewrite_holds model.interpretation formula joined).mp
          ((evalFormula_iff model (rewrite formula) joined).mp passes)
        refine (holds_agree model.interpretation formula ?_ within).mp holds
        intro name member
        simp only [joined, member, ↓reduceIte]
      · intro holds
        exact evalAll_complete model (fun valuation => (evalFormula_iff model (rewrite formula) valuation).mpr
          ((rewrite_holds model.interpretation formula valuation).mpr (holds valuation))) _ _
  · cases decided

inductive StepFailure where
  | rejected : Rejection → StepFailure
  | work

/-- Decide each statement in turn with one shared step budget; the steps left at the end. -/
def checkSteps (model : FiniteModel) : Nat → List Formula → Nat → Except StepFailure Nat
  | _, [], fuel => .ok fuel
  | index, formula :: rest, fuel =>
    match sentenceSteps model formula fuel with
    | .value true left => checkSteps model (index + 1) rest left
    | .value false _ => .error (.rejected (.statement index))
    | .scope => .error (.rejected (.scope index))
    | .work => .error .work

theorem checkSteps_sound (model : FiniteModel) :
    ∀ (formulas : List Formula) (index fuel left : Nat), checkSteps model index formulas fuel = .ok left →
      ∀ formula ∈ formulas, ∀ valuation, formula.Holds model.interpretation valuation := by
  intro formulas
  induction formulas with
  | nil => intro _ _ _ _ formula member; cases member
  | cons first others ih =>
    intro index fuel final accepted formula member
    simp only [checkSteps] at accepted
    split at accepted
    · rename_i rest decided
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact (sentenceSteps_iff decided).mp rfl
      · exact ih (index + 1) rest final accepted formula later
    · cases accepted
    · cases accepted
    · cases accepted

end Fang.TptpCandidate.FullFof.Model
