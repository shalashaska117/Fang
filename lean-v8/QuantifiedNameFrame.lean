/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Clause-name framing for the actual independent quantified decoder. -/
import QuantifiedInput
import Fang.FrontendClauseState

namespace Fang.QuantifiedFrontend
open Frontend

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

theorem binders_clauseProperty (property : List String → Prop) (fuel : Nat) :
    PreservesClauseProperty property (binders fuel) := by
  induction fuel with
  | zero => exact clauseProperty_fail _ _
  | succ fuel ih =>
      simp only [binders]
      apply clauseProperty_bind (clauseProperty_position property)
      intro offset
      apply clauseProperty_bind (clauseProperty_consume property)
      intro name
      split
      · exact clauseProperty_failAt_bind _ _ _ _
      · apply clauseProperty_bind (clauseProperty_variableId property name)
        intro id
        apply clauseProperty_bind (clauseProperty_peek property)
        intro delimiter
        split
        · exact clauseProperty_bind (clauseProperty_expect property "]")
            (fun _ => clauseProperty_pure _ _)
        · split
          · apply clauseProperty_bind (clauseProperty_expect property ",")
            intro ignored
            exact clauseProperty_bind ih (fun _ => clauseProperty_pure _ _)
          · split <;> exact clauseProperty_fail _ _

theorem binders_preserve_clause_names {fuel state encoded updated}
    (success : binders fuel state = .ok (encoded, updated)) :
    updated.clauseNames = state.clauseNames :=
  binders_clauseProperty (fun names => names = state.clauseNames) fuel
    state encoded updated rfl success

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
            · apply clauseProperty_bind (clauseProperty_discard_consume property)
              intro ignored
              apply clauseProperty_bind (clauseProperty_expect property "[")
              intro ignored
              apply clauseProperty_bind (binders_clauseProperty property fuel)
              intro names
              apply clauseProperty_bind (clauseProperty_expect property ":")
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
  formula_clauseProperty (fun names => names = state.clauseNames) fuel
    state encoded updated rfl success

end Fang.QuantifiedFrontend
