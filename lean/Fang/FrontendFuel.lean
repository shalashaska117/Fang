/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Fuel contracts for the actual source parser. Success preserves the complete
returned state, including token offsets and symbol tables.
-/
import Fang.FrontendParser

namespace Fang.Frontend

def Refines {α : Type} (first second : Parser α) : Prop :=
  ∀ (state : State) (value : α) (final : State),
    first state = .ok (value, final) → second state = .ok (value, final)

theorem refines_refl {α : Type} (parser : Parser α) : Refines parser parser := by
  intro state value final success
  exact success

theorem refines_trans {α : Type} {first second third : Parser α}
    (left : Refines first second) (right : Refines second third) : Refines first third := by
  intro state value final success
  exact right state value final (left state value final success)

theorem refines_bind {α β : Type} {first second : Parser α}
    {left right : α → Parser β} (head : Refines first second)
    (tail : ∀ value, Refines (left value) (right value)) :
    Refines (first >>= left) (second >>= right) := by
  intro state value final success
  cases execution : first state with
  | error error => simp [bind, StateT.bind, execution, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨intermediate, updated⟩
      have corresponding := head state intermediate updated execution
      simp only [bind, StateT.bind, execution, corresponding, Except.bind] at success ⊢
      exact tail intermediate updated value final success

theorem refines_failAt_bind {α β : Type} (offset : Nat) (reason : String)
    (continuation : α → Parser β) (other : Parser β) :
    Refines (failAt offset reason >>= continuation) other := by
  intro state value final success
  simp [bind, StateT.bind, failAt_run, Except.bind] at success

theorem refines_fail_bind {α β : Type} (reason : String)
    (continuation : α → Parser β) (other : Parser β) :
    Refines (fail reason >>= continuation) other := by
  intro state value final success
  simp [bind, StateT.bind, fail_run, Except.bind] at success

theorem term_refines_of_terms {fuel more : Nat}
    (arguments : Refines (terms fuel) (terms more)) :
    Refines (term (fuel + 1)) (term (more + 1)) := by
  simp only [term]
  apply refines_bind (refines_refl position)
  intro offset
  apply refines_bind (refines_refl consume)
  intro name
  split
  · exact refines_refl _
  · split
    · apply refines_bind (refines_refl (reserveSymbol false name))
      intro id
      apply refines_bind (refines_refl peek)
      intro next
      split
      · apply refines_bind (refines_refl (expect "("))
        intro _
        exact refines_bind arguments (fun _ => refines_refl _)
      · exact refines_refl _
    · exact refines_refl _

theorem terms_refines_of_terms {fuel more : Nat}
    (one : Refines (term fuel) (term more))
    (rest : Refines (terms fuel) (terms more)) :
    Refines (terms (fuel + 1)) (terms (more + 1)) := by
  simp only [terms]
  apply refines_bind one
  intro first
  apply refines_bind (refines_refl peek)
  intro next
  split
  · apply refines_bind (refines_refl (expect ","))
    intro _
    exact refines_bind rest (fun _ => refines_refl _)
  · exact refines_refl _

theorem term_terms_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (term fuel) (term more) ∧ Refines (terms fuel) (terms more) := by
  induction fuel generalizing more with
  | zero =>
      constructor <;> intro state value final success <;>
        simp [term, terms, fail_run] at success
  | succ fuel induction =>
      cases more with
      | zero => omega
      | succ more =>
          obtain ⟨one, rest⟩ := induction more (by omega)
          exact ⟨term_refines_of_terms rest, terms_refines_of_terms one rest⟩

theorem term_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (term fuel) (term more) := (term_terms_fuel_monotone fuel more enough).1

theorem terms_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (terms fuel) (terms more) := (term_terms_fuel_monotone fuel more enough).2

theorem literal_refines_of_terms {fuel more : Nat}
    (arguments : Refines (terms fuel) (terms more)) :
    Refines (literal fuel) (literal more) := by
  simp only [literal]
  apply refines_bind (refines_refl peek)
  intro next
  split <;> (try (apply refines_bind (refines_refl (expect "~")); intro ignored))
  all_goals
    apply refines_bind (refines_refl (pure _))
    intro positive
    apply refines_bind (refines_refl position)
    intro offset
    apply refines_bind (refines_refl consume)
    intro name
    split
    · exact refines_failAt_bind _ _ _ _
    · apply refines_bind (refines_refl (reserveSymbol true name))
      intro pred
      apply refines_bind (refines_refl peek)
      intro next
      split
      · apply refines_bind (refines_refl (expect "("))
        intro ignored
        exact refines_bind arguments (fun _ => refines_refl _)
      · exact refines_refl _

theorem literal_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (literal fuel) (literal more) :=
  literal_refines_of_terms (terms_fuel_monotone fuel more enough)

theorem literals_refines_of_literals {fuel more : Nat}
    (one : Refines (literal fuel) (literal more))
    (rest : Refines (literals fuel) (literals more)) :
    Refines (literals (fuel + 1)) (literals (more + 1)) := by
  simp only [literals]
  apply refines_bind one
  intro first
  apply refines_bind (refines_refl peek)
  intro next
  split
  · apply refines_bind (refines_refl (expect "|"))
    intro _
    exact refines_bind rest (fun _ => refines_refl _)
  · exact refines_refl _

theorem literals_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (literals fuel) (literals more) := by
  induction fuel generalizing more with
  | zero => intro state value final success; simp [literals, fail_run] at success
  | succ fuel induction =>
      cases more with
      | zero => omega
      | succ more =>
          exact literals_refines_of_literals (literal_fuel_monotone fuel more (by omega))
            (induction more (by omega))

theorem statement_refines_of_literals {fuel more : Nat}
    (body : Refines (literals fuel) (literals more)) :
    Refines (statement fuel) (statement more) := by
  simp only [statement]
  apply refines_bind (refines_refl peek)
  intro next
  split
  · exact refines_fail_bind _ _ _
  · apply refines_bind (refines_refl (expect "cnf"))
    intro ignored
    apply refines_bind (refines_refl (expect "("))
    intro ignored
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
        intro ignored
        apply refines_bind (refines_refl (expect ","))
        intro ignored
        apply refines_bind (refines_refl peek)
        intro next
        split
        · exact refines_fail_bind _ _ _
        · apply refines_bind (refines_refl (expect "axiom"))
          intro ignored
          apply refines_bind (refines_refl (expect ","))
          intro ignored
          apply refines_bind (refines_refl (expect "("))
          intro ignored
          apply refines_bind (refines_refl peek)
          intro next
          split
          · exact refines_refl _
          · exact refines_bind body (fun _ => refines_refl _)

theorem statement_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (statement fuel) (statement more) :=
  statement_refines_of_literals (literals_fuel_monotone fuel more enough)

theorem statements_fuel_monotone (fuel more : Nat) (enough : fuel ≤ more) :
    Refines (statements fuel) (statements more) := by
  induction fuel generalizing more with
  | zero => intro state value final success; simp [statements, fail_run] at success
  | succ fuel induction =>
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
            exact refines_bind (induction more (by omega)) (fun _ => refines_refl _)

#print axioms term_fuel_monotone
#print axioms terms_fuel_monotone
#print axioms literal_fuel_monotone
#print axioms literals_fuel_monotone
#print axioms statement_fuel_monotone
#print axioms statements_fuel_monotone

end Fang.Frontend
