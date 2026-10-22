/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Token-count bounds for successful executions of the actual parser.
-/
import Fang.FrontendFuel
import Fang.FrontendArity
import Fang.FrontendTokenPreservation

namespace Fang.Frontend

def Consumes {α : Type} (parser : Parser α) (minimum : Nat) : Prop :=
  ∀ (state : State) (value : α) (final : State),
    parser state = .ok (value, final) →
      final.tokens.length + minimum ≤ state.tokens.length

theorem consumes_weaken {α : Type} {parser : Parser α} {minimum less : Nat}
    (bound : Consumes parser minimum) (smaller : less ≤ minimum) :
    Consumes parser less := by
  intro state value final success
  have := bound state value final success
  omega

theorem consumes_pure {α : Type} (value : α) : Consumes (pure value) 0 := by
  intro state result final success
  have same : (value, state) = (result, final) := Except.ok.inj success
  cases same
  simp

theorem consumes_bind {α β : Type} {head : Parser α} {tail : α → Parser β}
    {first second : Nat} (before : Consumes head first)
    (after : ∀ value, Consumes (tail value) second) :
    Consumes (head >>= tail) (first + second) := by
  intro state value final success
  cases execution : head state with
  | error error => simp [bind, StateT.bind, execution, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨intermediate, updated⟩
      simp only [bind, StateT.bind, execution, Except.bind] at success
      have hfirst := before state intermediate updated execution
      have hsecond := after intermediate updated value final success
      omega

theorem consumes_bind_left {α β : Type} {head : Parser α} {tail : α → Parser β}
    {minimum : Nat} (before : Consumes head minimum)
    (after : ∀ value, Consumes (tail value) 0) :
    Consumes (head >>= tail) minimum := by
  simpa using consumes_bind before after

theorem consumes_bind_right {α β : Type} {head : Parser α} {tail : α → Parser β}
    {minimum : Nat} (before : Consumes head 0)
    (after : ∀ value, Consumes (tail value) minimum) :
    Consumes (head >>= tail) minimum := by
  simpa using consumes_bind before after

theorem consume_consumes : Consumes consume 1 := by
  intro state value final success
  obtain ⟨token, rest, tokens, _, rfl⟩ := consume_success success
  simp [tokens]

theorem expect_consumes (wanted : String) : Consumes (expect wanted) 1 := by
  intro state value final success
  cases value
  obtain ⟨token, rest, tokens, _, rfl⟩ := expect_success success
  simp [tokens]

theorem peek_consumes : Consumes peek 0 := by
  intro state value final success
  have same := Except.ok.inj success
  have final_eq : state = final := congrArg Prod.snd same
  subst final
  simp

theorem position_consumes : Consumes position 0 := by
  intro state value final success
  have same := Except.ok.inj success
  have final_eq : state = final := congrArg Prod.snd same
  subst final
  simp

theorem fail_consumes {α : Type} (reason : String) (minimum : Nat) :
    Consumes (fail (α := α) reason) minimum := by
  intro state value final success
  simp [fail_run] at success

theorem failAt_consumes {α : Type} (offset : Nat) (reason : String) (minimum : Nat) :
    Consumes (failAt (α := α) offset reason) minimum := by
  intro state value final success
  simp [failAt_run] at success

theorem variableId_consumes (name : String) : Consumes (variableId name) 0 := by
  intro state value final success
  simp [variableId_preserves_tokens name state final value success]

theorem reserveSymbol_consumes (predicate : Bool) (name : String) :
    Consumes (reserveSymbol predicate name) 0 := by
  intro state value final success
  simp [reserveSymbol_preserves_tokens predicate name state final value success]

theorem checkArity_consumes (predicate : Bool) (id arity offset : Nat) :
    Consumes (checkArity predicate id arity offset) 0 := by
  intro state value final success
  cases value
  simp [checkArity_preserves_tokens predicate id arity offset state final success]

theorem expect_consumes_zero (wanted : String) : Consumes (expect wanted) 0 :=
  consumes_weaken (expect_consumes wanted) (by omega)

theorem term_consumes_of_terms {fuel : Nat} (arguments : Consumes (terms fuel) 0) :
    Consumes (term (fuel + 1)) 1 := by
  simp only [term]
  apply consumes_bind_right position_consumes
  intro offset
  apply consumes_bind_left consume_consumes
  intro name
  split
  · exact consumes_bind_left (variableId_consumes name) (fun _ => consumes_pure _)
  · split
    · apply consumes_bind_left (reserveSymbol_consumes false name)
      intro id
      apply consumes_bind_left peek_consumes
      intro next
      split
      · apply consumes_bind_left (expect_consumes_zero "(")
        intro ignored
        apply consumes_bind_left arguments
        intro args
        apply consumes_bind_left (expect_consumes_zero ")")
        intro ignored
        apply consumes_bind_left (consumes_pure args)
        intro returnedArgs
        exact consumes_bind_left (checkArity_consumes false id returnedArgs.length offset)
          (fun _ => consumes_pure _)
      · apply consumes_bind_left (consumes_pure [])
        intro args
        exact consumes_bind_left (checkArity_consumes false id args.length offset)
          (fun _ => consumes_pure _)
    · exact failAt_consumes _ _ _

theorem terms_consumes_of_terms {fuel : Nat}
    (one : Consumes (term fuel) 1) (rest : Consumes (terms fuel) 0) :
    Consumes (terms (fuel + 1)) 1 := by
  simp only [terms]
  apply consumes_bind_left one
  intro first
  apply consumes_bind_left peek_consumes
  intro next
  split
  · apply consumes_bind_left (expect_consumes_zero ",")
    intro ignored
    exact consumes_bind_left rest (fun _ => consumes_pure _)
  · exact consumes_pure _

theorem term_terms_consumes (fuel : Nat) :
    Consumes (term fuel) 1 ∧ Consumes (terms fuel) 1 := by
  induction fuel with
  | zero => exact ⟨fail_consumes _ _, fail_consumes _ _⟩
  | succ fuel induction =>
      have rest : Consumes (terms fuel) 0 := consumes_weaken induction.2 (by omega)
      exact ⟨term_consumes_of_terms rest, terms_consumes_of_terms induction.1 rest⟩

theorem term_consumes (fuel : Nat) : Consumes (term fuel) 1 :=
  (term_terms_consumes fuel).1

theorem terms_consumes (fuel : Nat) : Consumes (terms fuel) 1 :=
  (term_terms_consumes fuel).2

theorem consumes_failAt_bind {α β : Type} (offset : Nat) (reason : String)
    (continuation : α → Parser β) (minimum : Nat) :
    Consumes (failAt offset reason >>= continuation) minimum := by
  intro state value final success
  simp [bind, StateT.bind, failAt_run, Except.bind] at success

theorem consumes_fail_bind {α β : Type} (reason : String)
    (continuation : α → Parser β) (minimum : Nat) :
    Consumes (fail reason >>= continuation) minimum := by
  intro state value final success
  simp [bind, StateT.bind, fail_run, Except.bind] at success

theorem literal_consumes (fuel : Nat) : Consumes (literal fuel) 1 := by
  simp only [literal]
  apply consumes_bind_right peek_consumes
  intro next
  split <;> (try (apply consumes_bind_right (expect_consumes_zero "~"); intro ignored))
  all_goals
    apply consumes_bind_right (consumes_pure _)
    intro positive
    apply consumes_bind_right position_consumes
    intro offset
    apply consumes_bind_left consume_consumes
    intro name
    split
    · exact consumes_failAt_bind _ _ _ _
    · apply consumes_bind_left (reserveSymbol_consumes true name)
      intro pred
      apply consumes_bind_left peek_consumes
      intro next
      split
      · apply consumes_bind_left (expect_consumes_zero "(")
        intro ignored
        apply consumes_bind_left (consumes_weaken (terms_consumes fuel) (by omega))
        intro args
        apply consumes_bind_left (expect_consumes_zero ")")
        intro ignored
        apply consumes_bind_left (consumes_pure args)
        intro returnedArgs
        exact consumes_bind_left (checkArity_consumes true pred returnedArgs.length offset)
          (fun _ => consumes_pure _)
      · apply consumes_bind_left (consumes_pure [])
        intro args
        exact consumes_bind_left (checkArity_consumes true pred args.length offset)
          (fun _ => consumes_pure _)

theorem literals_consumes (fuel : Nat) : Consumes (literals fuel) 1 := by
  induction fuel with
  | zero => exact fail_consumes _ _
  | succ fuel induction =>
      simp only [literals]
      apply consumes_bind_left (literal_consumes fuel)
      intro first
      apply consumes_bind_left peek_consumes
      intro next
      split
      · apply consumes_bind_left (expect_consumes_zero "|")
        intro ignored
        exact consumes_bind_left (consumes_weaken induction (by omega))
          (fun _ => consumes_pure _)
      · exact consumes_pure _

theorem clause_update_consumes {α : Type} (name : String) (offset minimum : Nat)
    (rest : Parser α) (bound : Consumes rest minimum) :
    Consumes (do
      let state ← get
      if state.clauseNames.contains name then
        failAt offset s!"invalid-syntax: duplicate clause name '{name}'"
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
  simp only [statement]
  apply consumes_bind_right peek_consumes
  intro next
  split
  · exact consumes_fail_bind _ _ _
  · apply consumes_bind_left (expect_consumes "cnf")
    intro ignored
    apply consumes_bind_left (expect_consumes_zero "(")
    intro ignored
    apply consumes_bind_left position_consumes
    intro offset
    apply consumes_bind_left (consumes_weaken consume_consumes (by omega))
    intro name
    split
    · exact consumes_failAt_bind _ _ _ _
    · apply clause_update_consumes name offset 0
      apply consumes_bind_left (expect_consumes_zero ",")
      intro ignored
      apply consumes_bind_left peek_consumes
      intro next
      split
      · exact consumes_fail_bind _ _ _
      · apply consumes_bind_left (expect_consumes_zero "axiom")
        intro ignored
        apply consumes_bind_left (expect_consumes_zero ",")
        intro ignored
        apply consumes_bind_left (expect_consumes_zero "(")
        intro ignored
        apply consumes_bind_left peek_consumes
        intro next
        split
        · apply consumes_bind_left (expect_consumes_zero "$false")
          intro ignored
          apply consumes_bind_left (consumes_pure [])
          intro body
          apply consumes_bind_left (expect_consumes_zero ")")
          intro ignored
          apply consumes_bind_left (expect_consumes_zero ")")
          intro ignored
          exact consumes_bind_left (expect_consumes_zero ".") (fun _ => consumes_pure _)
        · apply consumes_bind_left (consumes_weaken (literals_consumes fuel) (by omega))
          intro body
          apply consumes_bind_left (expect_consumes_zero ")")
          intro ignored
          apply consumes_bind_left (expect_consumes_zero ")")
          intro ignored
          exact consumes_bind_left (expect_consumes_zero ".") (fun _ => consumes_pure _)

theorem statements_consumes (fuel : Nat) : Consumes (statements fuel) 0 := by
  induction fuel with
  | zero => exact fail_consumes _ _
  | succ fuel induction =>
      simp only [statements]
      apply consumes_bind_left peek_consumes
      intro next
      split
      · exact consumes_pure _
      · apply consumes_bind_left (consumes_weaken (statement_consumes fuel) (by omega))
        intro first
        exact consumes_bind_left induction (fun _ => consumes_pure _)

#print axioms term_consumes
#print axioms terms_consumes
#print axioms literal_consumes
#print axioms literals_consumes
#print axioms statement_consumes
#print axioms statements_consumes

end Fang.Frontend
