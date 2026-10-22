/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Sufficient token-count fuel for reproducing successful parser executions.
This concerns the existing parser; grammar completeness is a separate theorem.
-/
import Fang.FrontendConsumption

namespace Fang.Frontend

def BoundedRefines {α : Type} (first second : Parser α) (available reserve : Nat) : Prop :=
  ∀ (state : State) (value : α) (final : State),
    state.tokens.length + reserve ≤ available →
    first state = .ok (value, final) → second state = .ok (value, final)

theorem boundedRefines_refl {α : Type} (parser : Parser α) (available reserve : Nat) :
    BoundedRefines parser parser available reserve := by
  intro state value final bound success
  exact success

theorem boundedRefines_of_refines {α : Type} {first second : Parser α}
    (refinement : Refines first second) (available reserve : Nat) :
    BoundedRefines first second available reserve := by
  intro state value final bound success
  exact refinement state value final success

theorem boundedRefines_change {α : Type} {first second : Parser α}
    {available reserve target margin : Nat}
    (refinement : BoundedRefines first second target margin)
    (transfer : ∀ n, n + reserve ≤ available → n + margin ≤ target) :
    BoundedRefines first second available reserve := by
  intro state value final bound success
  exact refinement state value final (transfer _ bound) success

theorem boundedRefines_bind {α β : Type} {first second : Parser α}
    {left right : α → Parser β} {available reserve consumed : Nat}
    (head : BoundedRefines first second available reserve)
    (consumption : Consumes first consumed)
    (tail : ∀ value, BoundedRefines (left value) (right value) available (reserve + consumed)) :
    BoundedRefines (first >>= left) (second >>= right) available reserve := by
  intro state value final bound success
  cases execution : first state with
  | error error => simp [bind, StateT.bind, execution, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨intermediate, updated⟩
      have corresponding := head state intermediate updated bound execution
      have used := consumption state intermediate updated execution
      simp only [bind, StateT.bind, execution, corresponding, Except.bind] at success ⊢
      exact tail intermediate updated value final (by omega) success

theorem boundedRefines_bind_same {α β : Type} (head : Parser α)
    {left right : α → Parser β} {available reserve consumed : Nat}
    (consumption : Consumes head consumed)
    (tail : ∀ value, BoundedRefines (left value) (right value) available (reserve + consumed)) :
    BoundedRefines (head >>= left) (head >>= right) available reserve :=
  boundedRefines_bind (boundedRefines_refl _ _ _) consumption tail

theorem boundedRefines_bind_changed {α β : Type} {first second : Parser α}
    (tail : α → Parser β) {available reserve : Nat}
    (head : BoundedRefines first second available reserve) :
    BoundedRefines (first >>= tail) (second >>= tail) available reserve := by
  intro state value final bound success
  cases execution : first state with
  | error error => simp [bind, StateT.bind, execution, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨intermediate, updated⟩
      have corresponding := head state intermediate updated bound execution
      simpa only [bind, StateT.bind, execution, corresponding, Except.bind] using success

theorem term_terms_fuel_sufficient (fuel : Nat) :
    (∀ more, BoundedRefines (term fuel) (term more) more 0) ∧
    (∀ more, BoundedRefines (terms fuel) (terms more) more 1) := by
  induction fuel with
  | zero =>
      constructor <;> intro more state value final bound success <;>
        simp [term, terms, fail_run] at success
  | succ fuel induction =>
      constructor
      · intro more
        cases more with
        | zero =>
            intro state value final bound success
            have used := term_consumes (fuel + 1) state value final success
            omega
        | succ more =>
            simp only [term]
            apply boundedRefines_bind_same position position_consumes
            intro offset
            apply boundedRefines_bind_same consume consume_consumes
            intro name
            split
            · exact boundedRefines_refl _ _ _
            · split
              · apply boundedRefines_bind_same (reserveSymbol false name)
                  (reserveSymbol_consumes false name)
                intro id
                apply boundedRefines_bind_same peek peek_consumes
                intro next
                split
                · apply boundedRefines_bind_same (expect "(") (expect_consumes "(")
                  intro ignored
                  apply boundedRefines_bind_changed
                  exact boundedRefines_change (induction.2 more) (by intro n h; omega)
                · exact boundedRefines_refl _ _ _
              · exact boundedRefines_refl _ _ _
      · intro more
        cases more with
        | zero => intro state value final bound success; omega
        | succ more =>
            simp only [terms]
            apply boundedRefines_bind
              (boundedRefines_change (induction.1 more) (by intro n h; omega))
              (term_consumes fuel)
            intro first
            apply boundedRefines_bind_same peek peek_consumes
            intro next
            split
            · apply boundedRefines_bind_same (expect ",") (expect_consumes ",")
              intro ignored
              apply boundedRefines_bind_changed
              exact boundedRefines_change (induction.2 more) (by intro n h; omega)
            · exact boundedRefines_refl _ _ _

theorem term_fuel_sufficient (fuel more : Nat) :
    BoundedRefines (term fuel) (term more) more 0 :=
  (term_terms_fuel_sufficient fuel).1 more

theorem terms_fuel_sufficient (fuel more : Nat) :
    BoundedRefines (terms fuel) (terms more) more 1 :=
  (term_terms_fuel_sufficient fuel).2 more

theorem literal_fuel_sufficient (fuel more : Nat) :
    BoundedRefines (literal fuel) (literal more) more 0 := by
  simp only [literal]
  apply boundedRefines_bind_same peek peek_consumes
  intro next
  split <;> (try (apply boundedRefines_bind_same (expect "~") (expect_consumes_zero "~"); intro ignored))
  all_goals
    apply boundedRefines_bind_same (pure _) (consumes_pure _)
    intro positive
    apply boundedRefines_bind_same position position_consumes
    intro offset
    apply boundedRefines_bind_same consume consume_consumes
    intro name
    split
    · exact boundedRefines_of_refines (refines_failAt_bind _ _ _ _) _ _
    · apply boundedRefines_bind_same (reserveSymbol true name) (reserveSymbol_consumes true name)
      intro pred
      apply boundedRefines_bind_same peek peek_consumes
      intro next
      split
      · apply boundedRefines_bind_same (expect "(") (expect_consumes "(")
        intro ignored
        apply boundedRefines_bind_changed
        exact boundedRefines_change (terms_fuel_sufficient fuel more) (by intro n h; omega)
      · exact boundedRefines_refl _ _ _

theorem literals_fuel_sufficient (fuel more : Nat) :
    BoundedRefines (literals fuel) (literals more) more 1 := by
  induction fuel generalizing more with
  | zero =>
      intro state value final bound success
      simp [literals, fail_run] at success
  | succ fuel induction =>
      cases more with
      | zero => intro state value final bound success; omega
      | succ more =>
          simp only [literals]
          apply boundedRefines_bind
            (boundedRefines_change (literal_fuel_sufficient fuel more) (by intro n h; omega))
            (literal_consumes fuel)
          intro first
          apply boundedRefines_bind_same peek peek_consumes
          intro next
          split
          · apply boundedRefines_bind_same (expect "|") (expect_consumes "|")
            intro ignored
            apply boundedRefines_bind_changed
            exact boundedRefines_change (induction more) (by intro n h; omega)
          · exact boundedRefines_refl _ _ _

theorem boundedRefines_clause_update {α : Type} (name : String) (offset : Nat)
    {left right : Parser α} {available reserve : Nat}
    (body : BoundedRefines left right available reserve) :
    BoundedRefines (do
      let state ← get
      if state.clauseNames.contains name then
        failAt offset s!"invalid-syntax: duplicate clause name '{name}'"
      set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
      left) (do
      let state ← get
      if state.clauseNames.contains name then
        failAt offset s!"invalid-syntax: duplicate clause name '{name}'"
      set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
      right) available reserve := by
  intro state value final bound success
  simp only [bind, get, getThe, MonadStateOf.get, StateT.bind, StateT.get,
    pure, Except.pure, Except.bind] at success ⊢
  split at success
  · simp [bind, StateT.bind, failAt_run, Except.bind] at success
  · rename_i unique
    simp only [unique]
    exact body { state with clauseNames := state.clauseNames ++ [name], variables := [] }
      value final bound success

theorem statement_fuel_sufficient (fuel more : Nat) :
    BoundedRefines (statement fuel) (statement more) more 0 := by
  simp only [statement]
  apply boundedRefines_bind_same peek peek_consumes
  intro next
  split
  · exact boundedRefines_of_refines (refines_fail_bind _ _ _) _ _
  · apply boundedRefines_bind_same (expect "cnf") (expect_consumes "cnf")
    intro ignored
    apply boundedRefines_bind_same (expect "(") (expect_consumes_zero "(")
    intro ignored
    apply boundedRefines_bind_same position position_consumes
    intro offset
    apply boundedRefines_bind_same consume (consumes_weaken (less := 0) consume_consumes (by omega))
    intro name
    split
    · exact boundedRefines_of_refines (refines_failAt_bind _ _ _ _) _ _
    · apply boundedRefines_clause_update name offset
      apply boundedRefines_bind_same (expect ",") (expect_consumes_zero ",")
      intro ignored
      apply boundedRefines_bind_same peek peek_consumes
      intro next
      split
      · exact boundedRefines_of_refines (refines_fail_bind _ _ _) _ _
      · apply boundedRefines_bind_same (expect "axiom") (expect_consumes_zero "axiom")
        intro ignored
        apply boundedRefines_bind_same (expect ",") (expect_consumes_zero ",")
        intro ignored
        apply boundedRefines_bind_same (expect "(") (expect_consumes_zero "(")
        intro ignored
        apply boundedRefines_bind_same peek peek_consumes
        intro next
        split
        · exact boundedRefines_refl _ _ _
        · apply boundedRefines_bind_changed
          exact boundedRefines_change (literals_fuel_sufficient fuel more) (by intro n h; omega)

theorem statements_fuel_sufficient (fuel more : Nat) :
    BoundedRefines (statements fuel) (statements more) more 1 := by
  induction fuel generalizing more with
  | zero =>
      intro state value final bound success
      simp [statements, fail_run] at success
  | succ fuel induction =>
      cases more with
      | zero => intro state value final bound success; omega
      | succ more =>
          simp only [statements]
          apply boundedRefines_bind_same peek peek_consumes
          intro next
          split
          · exact boundedRefines_refl _ _ _
          · apply boundedRefines_bind
              (boundedRefines_change (statement_fuel_sufficient fuel more) (by intro n h; omega))
              (statement_consumes fuel)
            intro first
            apply boundedRefines_bind_changed
            exact boundedRefines_change (induction more) (by intro n h; omega)

/-- The public token-count budget reproduces every success possible at any fuel. -/
theorem statements_token_count_fuel {fuel : Nat} {state final : State} {problem : Problem}
    (success : statements fuel state = .ok (problem, final)) :
    statements (state.tokens.length + 1) state = .ok (problem, final) :=
  statements_fuel_sufficient fuel (state.tokens.length + 1) state problem final
    (Nat.le_refl _) success

#print axioms term_fuel_sufficient
#print axioms terms_fuel_sufficient
#print axioms literal_fuel_sufficient
#print axioms literals_fuel_sufficient
#print axioms statement_fuel_sufficient
#print axioms statements_fuel_sufficient
#print axioms statements_token_count_fuel

end Fang.Frontend
