/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE.
   Successful actual parser executions preserve their full result when fuel grows. -/
import Fang.FOF.FOFInput
import Fang.FrontendFuel

namespace Fang.FOFFrontend
open Frontend

theorem formula_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (formula fuel) (formula more) := by
  induction fuel generalizing more with
  | zero => intro state value final success; simp [formula, fail_run] at success
  | succ fuel ih =>
    cases more with
    | zero => omega
    | succ more =>
      have child := ih more (by omega)
      simp only [formula]
      apply refines_bind (refines_refl peek)
      intro next
      split
      · exact refines_refl _
      · split
        · exact refines_refl _
        · split
          · apply refines_bind (refines_refl (expect "~"))
            intro _
            exact refines_bind child (fun _ => refines_refl _)
          · split
            · apply refines_bind (refines_refl (expect "("))
              intro _
              apply refines_bind child
              intro left
              apply refines_bind (refines_refl peek)
              intro operator
              split
              · apply refines_bind (refines_refl (discard consume))
                intro _
                exact refines_bind child (fun _ => refines_refl _)
              · exact refines_refl _
            · cases next with
              | none => exact refines_refl _
              | some name =>
                dsimp only
                split
                · exact refines_refl _
                · split
                  · exact refines_bind (Frontend.literal_fuel_monotone fuel more (by omega))
                      (fun _ => refines_refl _)
                  · exact refines_refl _

theorem statement_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (statement fuel) (statement more) := by
  unfold Fang.FOFFrontend.statement
  apply refines_bind (refines_refl peek)
  intro next
  split
  · exact refines_bind (Frontend.statement_fuel_monotone fuel more enough) (fun _ => refines_refl _)
  · apply refines_bind (refines_refl peek)
    intro next
    split
    · apply refines_bind (refines_refl (expect "fof"))
      intro _
      apply refines_bind (refines_refl (expect "("))
      intro _
      apply refines_bind (refines_refl position)
      intro offset
      apply refines_bind (refines_refl consume)
      intro name
      split
      · exact refines_failAt_bind _ _ _ _
      · apply refines_bind (refines_refl get)
        intro state
        split
        · exact refines_failAt_bind _ _ _ _
        · apply refines_bind (refines_refl (set _))
          intro _
          apply refines_bind (refines_refl (expect ","))
          intro _
          apply refines_bind (refines_refl peek)
          intro role
          split
          · exact refines_fail_bind _ _ _
          · apply refines_bind (refines_refl (expect "axiom"))
            intro _
            apply refines_bind (refines_refl (expect ","))
            intro _
            exact refines_bind (formula_fuel_monotone fuel more enough) (fun _ => refines_refl _)
    · exact refines_refl _

theorem statements_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (statements fuel) (statements more) := by
  induction fuel generalizing more with
  | zero => intro state value final success; simp [statements, fail_run] at success
  | succ fuel ih =>
    cases more with
    | zero => omega
    | succ more =>
      simp only [statements]
      apply refines_bind (refines_refl peek)
      intro next
      split
      · exact refines_refl _
      · apply refines_bind (statement_fuel_monotone fuel more (by omega))
        intro first
        exact refines_bind (ih more (by omega)) (fun _ => refines_refl _)

end Fang.FOFFrontend
