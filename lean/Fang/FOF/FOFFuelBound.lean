/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE.
   Token-count fuel reproduces every successful actual parser execution. -/
import Fang.FOF.FOFFuel
import Fang.FOF.FOFConsumption
import Fang.FrontendFuelBound

namespace Fang.FOFFrontend
open Frontend

theorem formula_fuel_sufficient (fuel more : Nat) :
    BoundedRefines (formula fuel) (formula more) more 1 := by
  induction fuel generalizing more with
  | zero => intro state value final bound success; simp [formula, fail_run] at success
  | succ fuel ih =>
    cases more with
    | zero => intro state value final bound success; omega
    | succ more =>
      simp only [formula]
      apply boundedRefines_bind_same peek peek_consumes
      intro next
      split
      · exact boundedRefines_refl _ _ _
      · split
        · exact boundedRefines_refl _ _ _
        · split
          · apply boundedRefines_bind_same (expect "~") (expect_consumes "~")
            intro _
            apply boundedRefines_bind_changed
            exact boundedRefines_change (ih more) (by intro n h; omega)
          · split
            · apply boundedRefines_bind_same (expect "(") (expect_consumes "(")
              intro _
              apply boundedRefines_bind
                (boundedRefines_change (ih more) (by intro n h; omega))
                (formula_consumes fuel)
              intro left
              apply boundedRefines_bind_same peek peek_consumes
              intro operator
              split
              · apply boundedRefines_bind_same (discard consume) (discard_consumes consume_consumes)
                intro _
                apply boundedRefines_bind_changed
                exact boundedRefines_change (ih more) (by intro n h; omega)
              · exact boundedRefines_refl _ _ _
            · cases next with
              | none => exact boundedRefines_refl _ _ _
              | some name =>
                dsimp only
                split
                · exact boundedRefines_refl _ _ _
                · split
                  · apply boundedRefines_bind_changed
                    exact boundedRefines_change (Frontend.literal_fuel_sufficient fuel more) (by intro n h; omega)
                  · exact boundedRefines_refl _ _ _

theorem boundedRefines_statement_update {α : Type} (name : String) (offset : Nat)
    {left right : Parser α} {available reserve : Nat}
    (body : BoundedRefines left right available reserve) :
    BoundedRefines (do
      let state ← get
      if state.clauseNames.contains name then failAt offset "invalid-syntax: duplicate statement name"
      set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
      left) (do
      let state ← get
      if state.clauseNames.contains name then failAt offset "invalid-syntax: duplicate statement name"
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
  unfold Fang.FOFFrontend.statement
  apply boundedRefines_bind_same peek peek_consumes
  intro next
  split
  · apply boundedRefines_bind_changed
    exact boundedRefines_change (Frontend.statement_fuel_sufficient fuel more) (by intro n h; omega)
  · apply boundedRefines_bind_same peek peek_consumes
    intro next
    split
    · apply boundedRefines_bind_same (expect "fof") (expect_consumes "fof")
      intro _
      apply boundedRefines_bind_same (expect "(") (expect_consumes_zero "(")
      intro _
      apply boundedRefines_bind_same position position_consumes
      intro offset
      apply boundedRefines_bind_same consume (consumes_weaken (less := 0) consume_consumes (by omega))
      intro name
      split
      · exact boundedRefines_of_refines (refines_failAt_bind _ _ _ _) _ _
      · apply boundedRefines_statement_update name offset
        apply boundedRefines_bind_same (expect ",") (expect_consumes_zero ",")
        intro _
        apply boundedRefines_bind_same peek peek_consumes
        intro role
        split
        · exact boundedRefines_of_refines (refines_fail_bind _ _ _) _ _
        · apply boundedRefines_bind_same (expect "axiom") (expect_consumes_zero "axiom")
          intro _
          apply boundedRefines_bind_same (expect ",") (expect_consumes_zero ",")
          intro _
          apply boundedRefines_bind_changed
          exact boundedRefines_change (formula_fuel_sufficient fuel more) (by intro n h; omega)
    · exact boundedRefines_refl _ _ _

theorem statements_fuel_sufficient (fuel more : Nat) :
    BoundedRefines (statements fuel) (statements more) more 1 := by
  induction fuel generalizing more with
  | zero => intro state value final bound success; simp [statements, fail_run] at success
  | succ fuel ih =>
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
        exact boundedRefines_change (ih more) (by intro n h; omega)

theorem formula_token_count_fuel {fuel : Nat} {state final : State} {value : GroundFOF.Formula}
    (success : formula fuel state = .ok (value, final)) :
    formula (state.tokens.length + 1) state = .ok (value, final) :=
  formula_fuel_sufficient fuel (state.tokens.length + 1) state value final (Nat.le_refl _) success

theorem statement_token_count_fuel {fuel : Nat} {state final : State} {value : GroundFOF.Declaration}
    (success : statement fuel state = .ok (value, final)) :
    statement state.tokens.length state = .ok (value, final) :=
  statement_fuel_sufficient fuel state.tokens.length state value final (by omega) success

/-- This is exactly the initial token-count budget used by `decode`. -/
theorem statements_token_count_fuel {fuel : Nat} {state final : State} {value : List GroundFOF.Declaration}
    (success : statements fuel state = .ok (value, final)) :
    statements (state.tokens.length + 1) state = .ok (value, final) :=
  statements_fuel_sufficient fuel (state.tokens.length + 1) state value final (Nat.le_refl _) success

end Fang.FOFFrontend
