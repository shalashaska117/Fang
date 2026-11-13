/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFInput
import Fang.FrontendConsumption

namespace Fang.FOFFrontend
open Frontend

theorem discard_consumes {α : Type} {parser : Parser α} {minimum : Nat}
    (bound : Consumes parser minimum) : Consumes (discard parser) minimum := by
  intro state value final success
  cases execution : parser state with
  | error error =>
      simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, execution] at success
  | ok pair =>
      rcases pair with ⟨result, updated⟩
      simp [discard, Functor.mapConst, Functor.map, StateT.map, Except.map, execution] at success
      rcases success with ⟨rfl, rfl⟩
      exact bound state result final execution

theorem formula_consumes (fuel : Nat) : Consumes (formula fuel) 1 := by
  induction fuel with
  | zero => exact fail_consumes _ _
  | succ fuel ih =>
    have child : Consumes (formula fuel) 0 := consumes_weaken ih (by omega)
    simp only [formula]
    apply consumes_bind_right peek_consumes
    intro next
    split
    · exact consumes_bind_left (expect_consumes "$true") (fun _ => consumes_pure _)
    · split
      · exact consumes_bind_left (expect_consumes "$false") (fun _ => consumes_pure _)
      · split
        · apply consumes_bind_left (expect_consumes "~")
          intro _
          exact consumes_bind_left child (fun _ => consumes_pure _)
        · split
          · apply consumes_bind_left (expect_consumes "(")
            intro _
            apply consumes_bind_left child
            intro left
            apply consumes_bind_left peek_consumes
            intro operator
            split
            · apply consumes_bind_left (consumes_weaken (discard_consumes consume_consumes) (Nat.zero_le 1))
              intro _
              apply consumes_bind_left child
              intro right
              apply consumes_bind_left (expect_consumes_zero ")")
              intro _
              split
              · exact consumes_pure _
              · split <;> exact consumes_pure _
            · exact consumes_bind_left (expect_consumes_zero ")") (fun _ => consumes_pure _)
          · cases next with
            | none => exact fail_consumes _ _
            | some name =>
              dsimp only
              split
              · exact fail_consumes _ _
              · split
                · exact consumes_bind_left (literal_consumes fuel) (fun _ => consumes_pure _)
                · exact fail_consumes _ _

theorem statement_name_update_consumes {α : Type} (name : String) (offset minimum : Nat)
    (rest : Parser α) (bound : Consumes rest minimum) :
    Consumes (do
      let state ← get
      if state.clauseNames.contains name then
        failAt offset "invalid-syntax: duplicate statement name"
      set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
      rest) minimum := by
  intro state value final success
  simp only [bind, get, getThe, MonadStateOf.get, StateT.bind, StateT.get,
    pure, Except.pure, Except.bind] at success
  split at success
  · simp [bind, StateT.bind, failAt_run, Except.bind] at success
  · exact bound { state with clauseNames := state.clauseNames ++ [name], variables := [] }
      value final success

theorem statement_consumes (fuel : Nat) : Consumes (statement fuel) 1 := by
  unfold Fang.FOFFrontend.statement
  apply consumes_bind_right peek_consumes
  intro next
  split
  · exact consumes_bind_left (Frontend.statement_consumes fuel) (fun _ => consumes_pure _)
  · apply consumes_bind_right peek_consumes
    intro next
    split
    · apply consumes_bind_left (expect_consumes "fof")
      intro _
      apply consumes_bind_left (expect_consumes_zero "(")
      intro _
      apply consumes_bind_left position_consumes
      intro offset
      apply consumes_bind_left (consumes_weaken consume_consumes (by omega))
      intro name
      split
      · exact consumes_failAt_bind _ _ _ _
      · apply statement_name_update_consumes name offset 0
        apply consumes_bind_left (expect_consumes_zero ",")
        intro _
        apply consumes_bind_left peek_consumes
        intro role
        split
        · exact consumes_fail_bind _ _ _
        · apply consumes_bind_left (expect_consumes_zero "axiom")
          intro _
          apply consumes_bind_left (expect_consumes_zero ",")
          intro _
          apply consumes_bind_left (consumes_weaken (formula_consumes fuel) (by omega))
          intro body
          split
          · exact consumes_fail_bind _ _ _
          · apply consumes_bind_left peek_consumes
            intro annotation
            split
            · exact consumes_fail_bind _ _ _
            · apply consumes_bind_left (expect_consumes_zero ")")
              intro _
              exact consumes_bind_left (expect_consumes_zero ".") (fun _ => consumes_pure _)
    · exact fail_consumes _ _

theorem statements_consumes (fuel : Nat) : Consumes (statements fuel) 0 := by
  induction fuel with
  | zero => exact fail_consumes _ _
  | succ fuel ih =>
    simp only [statements]
    apply consumes_bind_left peek_consumes
    intro next
    split
    · exact consumes_pure _
    · apply consumes_bind_left (consumes_weaken (statement_consumes fuel) (by omega))
      intro _
      exact consumes_bind_left ih (fun _ => consumes_pure _)

theorem statements_exhaust (fuel : Nat) (initial final : State)
    (declarations : List GroundFOF.Declaration)
    (success : statements fuel initial = .ok (declarations, final)) :
    final.tokens = [] := by
  induction fuel generalizing initial final declarations with
  | zero => simp [statements, fail_run] at success
  | succ fuel ih =>
    rw [Fang.FOFFrontend.statements] at success
    simp only [bind, StateT.bind, peek_run, Except.bind] at success
    split at success
    · have same := Except.ok.inj success
      have final_eq : initial = final := congrArg Prod.snd same
      subst final
      cases tokens : initial.tokens with
      | nil => rfl
      | cons head tail => simp [tokens] at *
    · cases execution : statement fuel initial with
      | error error => simp [execution, bind, StateT.bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨first, middle⟩
        simp only [execution, bind, StateT.bind, Except.bind] at success
        cases remaining : statements fuel middle with
        | error error => simp [remaining] at success
        | ok pair =>
          rcases pair with ⟨rest, last⟩
          simp only [remaining] at success
          have same := Except.ok.inj success
          have final_eq : last = final := congrArg Prod.snd same
          subst final
          exact ih middle last rest remaining

theorem decode_exhausts {input result} (success : decode input = .ok result) :
    result.state.tokens = [] := by
  unfold decode at success
  cases scanned : tokenize input with
  | error error => simp [scanned, bind, Except.bind] at success
  | ok tokens =>
    simp only [scanned, bind, Except.bind] at success
    cases parsed : statements (tokens.length + 1) { tokens, endOffset := input.utf8ByteSize } with
    | error error => simp [parsed] at success
    | ok pair =>
      rcases pair with ⟨declarations, final⟩
      simp only [parsed] at success
      have same := Except.ok.inj success
      cases same
      exact statements_exhaust _ _ _ _ parsed

end Fang.FOFFrontend
