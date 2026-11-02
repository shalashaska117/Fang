/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFEncodingRun

namespace Fang.FOFFrontend
open Frontend

theorem expect_clause_names {wanted state updated}
    (success : expect wanted state = .ok ((), updated)) :
    updated.clauseNames = state.clauseNames :=
  clauseProperty_expect (fun names => names = state.clauseNames) wanted state () updated rfl success

theorem consume_clause_names {name state updated}
    (success : consume state = .ok (name, updated)) :
    updated.clauseNames = state.clauseNames :=
  clauseProperty_consume (fun names => names = state.clauseNames) state name updated rfl success

theorem clauseProperty_discard_consume (property : List String → Prop) :
    PreservesClauseProperty property (discard consume) := by
  intro state value final valid success
  cases consumed : consume state with
  | error error =>
      simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, consumed] at success
  | ok pair =>
      rcases pair with ⟨text, updated⟩
      simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, consumed] at success
      rcases success with ⟨rfl, rfl⟩
      exact clauseProperty_consume property state text final valid consumed

theorem formula_clauseProperty (property : List String → Prop) (fuel : Nat) :
    PreservesClauseProperty property (formula fuel) := by
  induction fuel with
  | zero => exact clauseProperty_fail _ _
  | succ fuel ih =>
      simp only [formula]
      apply clauseProperty_bind (clauseProperty_peek property)
      intro next
      split
      · exact clauseProperty_bind (clauseProperty_expect property "$true")
          (fun _ => clauseProperty_pure _ _)
      · split
        · exact clauseProperty_bind (clauseProperty_expect property "$false")
            (fun _ => clauseProperty_pure _ _)
        · split
          · apply clauseProperty_bind (clauseProperty_expect property "~")
            intro ignored
            exact clauseProperty_bind ih (fun _ => clauseProperty_pure _ _)
          · split
            · apply clauseProperty_bind (clauseProperty_expect property "(")
              intro ignored
              apply clauseProperty_bind ih
              intro left
              apply clauseProperty_bind (clauseProperty_peek property)
              intro operator
              split
              · apply clauseProperty_bind (clauseProperty_discard_consume property)
                intro ignored
                apply clauseProperty_bind ih
                intro right
                apply clauseProperty_bind (clauseProperty_expect property ")")
                intro ignored
                split
                · exact clauseProperty_pure _ _
                · split <;> exact clauseProperty_pure _ _
              · exact clauseProperty_bind (clauseProperty_expect property ")")
                  (fun _ => clauseProperty_pure _ _)
            · split
              · split
                · exact clauseProperty_fail _ _
                · split
                  · exact clauseProperty_bind (clauseProperty_literal property fuel)
                      (fun _ => clauseProperty_pure _ _)
                  · exact clauseProperty_fail _ _
              · exact clauseProperty_fail _ _

theorem formula_preserves_clause_names {fuel state encoded updated}
    (success : formula fuel state = .ok (encoded, updated)) :
    updated.clauseNames = state.clauseNames :=
  formula_clauseProperty (fun names => names = state.clauseNames) fuel state encoded updated rfl success

end Fang.FOFFrontend
