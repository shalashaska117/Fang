/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Clause-name invariants of the actual independent decoder. These contracts do
not establish the correspondence between returned clauses and source syntax.
-/
import Fang.FrontendArity

namespace Fang.Frontend

def PreservesClauseProperty {α : Type} (property : List String → Prop)
    (parser : Parser α) : Prop :=
  ∀ (state : State) (value : α) (final : State), property state.clauseNames →
    parser state = .ok (value, final) → property final.clauseNames

theorem clauseProperty_bind {α β : Type} {property : List String → Prop}
    {head : Parser α} {tail : α → Parser β}
    (before : PreservesClauseProperty property head)
    (after : ∀ value, PreservesClauseProperty property (tail value)) :
    PreservesClauseProperty property (head >>= tail) := by
  intro state value final valid success
  cases execution : head state with
  | error error => simp [bind, StateT.bind, execution, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨intermediate, updated⟩
      simp only [bind, StateT.bind, execution, Except.bind] at success
      exact after intermediate updated value final (before state intermediate updated valid execution) success

theorem clauseProperty_frame {α : Type} {property : List String → Prop}
    {parser : Parser α}
    (frame : ∀ state value final, parser state = .ok (value, final) →
      final.clauseNames = state.clauseNames) : PreservesClauseProperty property parser := by
  intro state value final valid success
  simpa only [frame state value final success] using valid

theorem clauseProperty_pure {α : Type} (property : List String → Prop) (value : α) :
    PreservesClauseProperty property (pure value) := by
  apply clauseProperty_frame
  intro state result final success
  have same : (value, state) = (result, final) := Except.ok.inj success
  cases same
  rfl

theorem clauseProperty_peek (property : List String → Prop) :
    PreservesClauseProperty property peek := by
  apply clauseProperty_frame
  intro state value final success
  have same := congrArg Prod.snd (Except.ok.inj success)
  cases same
  rfl

theorem clauseProperty_position (property : List String → Prop) :
    PreservesClauseProperty property position := by
  apply clauseProperty_frame
  intro state value final success
  have same := congrArg Prod.snd (Except.ok.inj success)
  cases same
  rfl

theorem clauseProperty_consume (property : List String → Prop) :
    PreservesClauseProperty property consume := by
  apply clauseProperty_frame
  intro state value final success
  obtain ⟨token, rest, _, _, rfl⟩ := consume_success success
  rfl

theorem clauseProperty_expect (property : List String → Prop) (wanted : String) :
    PreservesClauseProperty property (expect wanted) := by
  apply clauseProperty_frame
  intro state value final success
  cases value
  obtain ⟨token, rest, _, _, rfl⟩ := expect_success success
  rfl

theorem clauseProperty_fail {α : Type} (property : List String → Prop) (reason : String) :
    PreservesClauseProperty property (fail (α := α) reason) := by
  intro state value final valid success
  simp [fail_run] at success

theorem clauseProperty_failAt {α : Type} (property : List String → Prop)
    (offset : Nat) (reason : String) :
    PreservesClauseProperty property (failAt (α := α) offset reason) := by
  intro state value final valid success
  simp [failAt_run] at success

theorem clauseProperty_fail_bind {α β : Type} (property : List String → Prop)
    (reason : String) (tail : α → Parser β) :
    PreservesClauseProperty property (fail reason >>= tail) := by
  intro state value final valid success
  simp [bind, StateT.bind, fail_run, Except.bind] at success

theorem clauseProperty_failAt_bind {α β : Type} (property : List String → Prop)
    (offset : Nat) (reason : String) (tail : α → Parser β) :
    PreservesClauseProperty property (failAt offset reason >>= tail) := by
  intro state value final valid success
  simp [bind, StateT.bind, failAt_run, Except.bind] at success

theorem clauseProperty_variableId (property : List String → Prop) (name : String) :
    PreservesClauseProperty property (variableId name) := by
  apply clauseProperty_frame
  intro state value final success
  obtain ⟨actualId, actualState, actualRun, _, _, _, _, _, names⟩ := variableId_spec name state
  rw [success] at actualRun
  cases actualRun
  exact names

theorem clauseProperty_reserveSymbol (property : List String → Prop)
    (predicate : Bool) (name : String) :
    PreservesClauseProperty property (reserveSymbol predicate name) := by
  apply clauseProperty_frame
  intro state value final success
  obtain ⟨actualId, actualState, actualRun, _, _, _, _, names, _⟩ := reserveSymbol_spec predicate name state
  rw [success] at actualRun
  cases actualRun
  exact names

theorem clauseProperty_checkArity (property : List String → Prop)
    (predicate : Bool) (id arity offset : Nat) :
    PreservesClauseProperty property (checkArity predicate id arity offset) := by
  apply clauseProperty_frame
  intro state value final success
  cases value
  rw [checkArity_run] at success
  cases found : (symbolTable state predicate)[id]? with
  | none => simp [found, fail_run] at success
  | some symbol =>
      rw [found] at success
      cases previous : symbol.arity with
      | some previousArity =>
          simp only [previous] at success
          split at success
          · simp [failAt_run] at success
          · cases success; rfl
      | none =>
          simp only [previous] at success
          cases success
          cases predicate <;> rfl

theorem clauseProperty_term_of_terms (property : List String → Prop) {fuel : Nat}
    (arguments : PreservesClauseProperty property (terms fuel)) :
    PreservesClauseProperty property (term (fuel + 1)) := by
  simp only [term]
  apply clauseProperty_bind (clauseProperty_position property)
  intro offset
  apply clauseProperty_bind (clauseProperty_consume property)
  intro name
  split
  · exact clauseProperty_bind (clauseProperty_variableId property name) (fun _ => clauseProperty_pure _ _)
  · split
    · apply clauseProperty_bind (clauseProperty_reserveSymbol property false name)
      intro id
      apply clauseProperty_bind (clauseProperty_peek property)
      intro next
      split
      · apply clauseProperty_bind (clauseProperty_expect property "(")
        intro ignored
        apply clauseProperty_bind arguments
        intro args
        apply clauseProperty_bind (clauseProperty_expect property ")")
        intro ignored
        apply clauseProperty_bind (clauseProperty_pure property args)
        intro returnedArgs
        exact clauseProperty_bind (clauseProperty_checkArity property false id returnedArgs.length offset)
          (fun _ => clauseProperty_pure _ _)
      · apply clauseProperty_bind (clauseProperty_pure property [])
        intro args
        exact clauseProperty_bind (clauseProperty_checkArity property false id args.length offset)
          (fun _ => clauseProperty_pure _ _)
    · exact clauseProperty_failAt _ _ _

theorem clauseProperty_terms_of_terms (property : List String → Prop) {fuel : Nat}
    (one : PreservesClauseProperty property (term fuel))
    (rest : PreservesClauseProperty property (terms fuel)) :
    PreservesClauseProperty property (terms (fuel + 1)) := by
  simp only [terms]
  apply clauseProperty_bind one
  intro first
  apply clauseProperty_bind (clauseProperty_peek property)
  intro next
  split
  · apply clauseProperty_bind (clauseProperty_expect property ",")
    intro ignored
    exact clauseProperty_bind rest (fun _ => clauseProperty_pure _ _)
  · exact clauseProperty_pure _ _

theorem clauseProperty_term_terms (property : List String → Prop) (fuel : Nat) :
    PreservesClauseProperty property (term fuel) ∧
    PreservesClauseProperty property (terms fuel) := by
  induction fuel with
  | zero => exact ⟨clauseProperty_fail _ _, clauseProperty_fail _ _⟩
  | succ fuel induction => exact ⟨clauseProperty_term_of_terms property induction.2,
      clauseProperty_terms_of_terms property induction.1 induction.2⟩

theorem clauseProperty_literal (property : List String → Prop) (fuel : Nat) :
    PreservesClauseProperty property (literal fuel) := by
  simp only [literal]
  apply clauseProperty_bind (clauseProperty_peek property)
  intro next
  split
  · apply clauseProperty_bind (clauseProperty_expect property "~")
    intro ignored
    apply clauseProperty_bind (clauseProperty_pure property false)
    intro positive
    apply clauseProperty_bind (clauseProperty_position property)
    intro offset
    apply clauseProperty_bind (clauseProperty_consume property)
    intro name
    split
    · exact clauseProperty_failAt_bind _ _ _ _
    · apply clauseProperty_bind (clauseProperty_reserveSymbol property true name)
      intro pred
      apply clauseProperty_bind (clauseProperty_peek property)
      intro next
      split
      · apply clauseProperty_bind (clauseProperty_expect property "(")
        intro ignored
        apply clauseProperty_bind (clauseProperty_term_terms property fuel).2
        intro args
        apply clauseProperty_bind (clauseProperty_expect property ")")
        intro ignored
        apply clauseProperty_bind (clauseProperty_pure property args)
        intro returnedArgs
        exact clauseProperty_bind (clauseProperty_checkArity property true pred returnedArgs.length offset)
          (fun _ => clauseProperty_pure _ _)
      · apply clauseProperty_bind (clauseProperty_pure property [])
        intro args
        exact clauseProperty_bind (clauseProperty_checkArity property true pred args.length offset)
          (fun _ => clauseProperty_pure _ _)
  · apply clauseProperty_bind (clauseProperty_pure property true)
    intro positive
    apply clauseProperty_bind (clauseProperty_position property)
    intro offset
    apply clauseProperty_bind (clauseProperty_consume property)
    intro name
    split
    · exact clauseProperty_failAt_bind _ _ _ _
    · apply clauseProperty_bind (clauseProperty_reserveSymbol property true name)
      intro pred
      apply clauseProperty_bind (clauseProperty_peek property)
      intro next
      split
      · apply clauseProperty_bind (clauseProperty_expect property "(")
        intro ignored
        apply clauseProperty_bind (clauseProperty_term_terms property fuel).2
        intro args
        apply clauseProperty_bind (clauseProperty_expect property ")")
        intro ignored
        apply clauseProperty_bind (clauseProperty_pure property args)
        intro returnedArgs
        exact clauseProperty_bind (clauseProperty_checkArity property true pred returnedArgs.length offset)
          (fun _ => clauseProperty_pure _ _)
      · apply clauseProperty_bind (clauseProperty_pure property [])
        intro args
        exact clauseProperty_bind (clauseProperty_checkArity property true pred args.length offset)
          (fun _ => clauseProperty_pure _ _)

theorem clauseProperty_literals (property : List String → Prop) (fuel : Nat) :
    PreservesClauseProperty property (literals fuel) := by
  induction fuel with
  | zero => exact clauseProperty_fail _ _
  | succ fuel induction =>
      simp only [literals]
      apply clauseProperty_bind (clauseProperty_literal property fuel)
      intro first
      apply clauseProperty_bind (clauseProperty_peek property)
      intro next
      split
      · apply clauseProperty_bind (clauseProperty_expect property "|")
        intro ignored
        exact clauseProperty_bind induction (fun _ => clauseProperty_pure _ _)
      · exact clauseProperty_pure _ _

theorem clause_update_unique {α : Type} (name : String) (offset : Nat)
    (rest : Parser α) (preserved : PreservesClauseProperty List.Nodup rest) :
    PreservesClauseProperty List.Nodup (do
      let state ← get
      if state.clauseNames.contains name then
        failAt offset s!"invalid-syntax: duplicate clause name '{name}'"
      set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
      rest) := by
  intro state value final valid success
  simp only [bind, get, getThe, MonadStateOf.get, StateT.bind, StateT.get,
    pure, Except.pure, Except.bind] at success
  split at success
  · simp [bind, StateT.bind, failAt_run, Except.bind] at success
  · rename_i fresh
    have absent : name ∉ state.clauseNames := by simpa using fresh
    have extended : (state.clauseNames ++ [name]).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨valid, by simp, ?_⟩
      intro left member right singleton
      have same : right = name := by simpa using singleton
      subst right
      intro equal
      exact absent (equal ▸ member)
    exact preserved { state with clauseNames := state.clauseNames ++ [name], variables := [] }
      value final extended success

theorem statement_preserves_unique_clause_names (fuel : Nat) :
    PreservesClauseProperty List.Nodup (statement fuel) := by
  simp only [statement]
  apply clauseProperty_bind (clauseProperty_peek List.Nodup)
  intro next
  split
  · exact clauseProperty_fail_bind List.Nodup _ _
  · apply clauseProperty_bind (clauseProperty_expect List.Nodup "cnf")
    intro ignored
    apply clauseProperty_bind (clauseProperty_expect List.Nodup "(")
    intro ignored
    apply clauseProperty_bind (clauseProperty_position List.Nodup)
    intro offset
    apply clauseProperty_bind (clauseProperty_consume List.Nodup)
    intro name
    split
    · exact clauseProperty_failAt_bind List.Nodup _ _ _
    · apply clause_update_unique name offset
      apply clauseProperty_bind (clauseProperty_expect List.Nodup ",")
      intro ignored
      apply clauseProperty_bind (clauseProperty_peek List.Nodup)
      intro next
      split
      · exact clauseProperty_fail_bind List.Nodup _ _
      · apply clauseProperty_bind (clauseProperty_expect List.Nodup "axiom")
        intro ignored
        apply clauseProperty_bind (clauseProperty_expect List.Nodup ",")
        intro ignored
        apply clauseProperty_bind (clauseProperty_expect List.Nodup "(")
        intro ignored
        apply clauseProperty_bind (clauseProperty_peek List.Nodup)
        intro next
        split
        · apply clauseProperty_bind (clauseProperty_expect List.Nodup "$false")
          intro ignored
          apply clauseProperty_bind (clauseProperty_pure List.Nodup [])
          intro body
          apply clauseProperty_bind (clauseProperty_expect List.Nodup ")")
          intro ignored
          apply clauseProperty_bind (clauseProperty_expect List.Nodup ")")
          intro ignored
          exact clauseProperty_bind (clauseProperty_expect List.Nodup ".") (fun _ => clauseProperty_pure List.Nodup _)
        · apply clauseProperty_bind (clauseProperty_literals List.Nodup fuel)
          intro body
          apply clauseProperty_bind (clauseProperty_expect List.Nodup ")")
          intro ignored
          apply clauseProperty_bind (clauseProperty_expect List.Nodup ")")
          intro ignored
          exact clauseProperty_bind (clauseProperty_expect List.Nodup ".") (fun _ => clauseProperty_pure List.Nodup _)

theorem statements_preserve_unique_clause_names (fuel : Nat) :
    PreservesClauseProperty List.Nodup (statements fuel) := by
  induction fuel with
  | zero => exact clauseProperty_fail List.Nodup _
  | succ fuel induction =>
      simp only [statements]
      apply clauseProperty_bind (clauseProperty_peek List.Nodup)
      intro next
      split
      · exact clauseProperty_pure List.Nodup _
      · apply clauseProperty_bind (statement_preserves_unique_clause_names fuel)
        intro first
        exact clauseProperty_bind induction (fun _ => clauseProperty_pure List.Nodup _)

theorem literals_preserve_clause_names {fuel : Nat} {state final : State} {clause : Clause}
    (success : literals fuel state = .ok (clause, final)) :
    final.clauseNames = state.clauseNames :=
  clauseProperty_literals (fun names => names = state.clauseNames) fuel state clause final rfl success

theorem parser_bind_success {α β : Type} {head : Parser α} {tail : α → Parser β}
    {state final : State} {value : β}
    (success : (head >>= tail) state = .ok (value, final)) :
    ∃ intermediate updated, head state = .ok (intermediate, updated) ∧
      tail intermediate updated = .ok (value, final) := by
  cases execution : head state with
  | error error => simp [bind, StateT.bind, execution, Except.bind] at success
  | ok pair =>
      rcases pair with ⟨intermediate, updated⟩
      exact ⟨intermediate, updated, rfl,
        by simpa [bind, StateT.bind, execution, Except.bind] using success⟩

theorem clause_update_success_iff {α : Type} (name : String) (offset : Nat)
    (rest : Parser α) (state final : State) (value : α) :
    ((do
      let before : State ← get
      if before.clauseNames.contains name then
        failAt offset s!"invalid-syntax: duplicate clause name '{name}'"
      set { before with clauseNames := before.clauseNames ++ [name], variables := [] }
      rest : Parser α) state = .ok (value, final)) ↔
    name ∉ state.clauseNames ∧
      rest { state with clauseNames := state.clauseNames ++ [name], variables := [] } =
        .ok (value, final) := by
  simp only [bind, get, getThe, MonadStateOf.get, StateT.bind, StateT.get,
    pure, Except.pure, Except.bind]
  by_cases present : name ∈ state.clauseNames
  · simp [present, bind, StateT.bind, failAt_run, Except.bind]
  · simp [present, bind, StateT.bind, set, StateT.set, Except.bind, pure, Except.pure]

/- This predicate names the exact remaining commands of `statement`, not a
   replacement parser. The decomposition theorem connects it to actual runs. -/
def StatementTailRun (fuel : Nat) (state : State) (clause : Clause) (final : State) : Prop :=
  (do
    expect ","
    if (← peek) != some "axiom" then fail "unsupported: only the axiom role is supported"
    expect "axiom"
    expect ","
    expect "("
    let body ← if (← peek) == some "$false" then expect "$false"; pure []
      else literals fuel
    expect ")"
    expect ")"
    expect "."
    pure body : Parser Clause) state = .ok (clause, final)

theorem statement_success_decomposition {fuel : Nat} {state final : State} {clause : Clause}
    (success : statement fuel state = .ok (clause, final)) :
    ∃ name afterCnf opened named,
      expect "cnf" state = .ok ((), afterCnf) ∧
      expect "(" afterCnf = .ok ((), opened) ∧
      consume opened = .ok (name, named) ∧ lowerName name = true ∧
      name ∉ named.clauseNames ∧
      named.clauseNames = state.clauseNames ∧ named.variables = state.variables ∧
      StatementTailRun fuel
        { named with clauseNames := named.clauseNames ++ [name], variables := [] } clause final := by
  simp only [statement] at success
  obtain ⟨next, before, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  split at success
  · simp [bind, StateT.bind, fail_run, Except.bind] at success
  · obtain ⟨ignored, afterCnf, cnf, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨ignored, opened, opening, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨offset, positioned, positionRun, success⟩ := parser_bind_success success
    have same : ((match opened.tokens with
      | [] => opened.endOffset
      | token :: _ => token.offset), opened) = (offset, positioned) := Except.ok.inj positionRun
    cases same
    obtain ⟨name, named, consumed, success⟩ := parser_bind_success success
    split at success
    · simp [bind, StateT.bind, failAt_run, Except.bind] at success
    · rename_i validName
      have nameValid : lowerName name = true := by simpa using validName
      obtain ⟨fresh, tail⟩ := (clause_update_success_iff name _ _ named final clause).mp success
      have frameCnf := expect_success cnf
      have frameOpening := expect_success opening
      have frameName := consume_success consumed
      obtain ⟨_, _, _, _, cnfState⟩ := frameCnf
      obtain ⟨_, _, _, _, openingState⟩ := frameOpening
      obtain ⟨_, _, _, _, nameState⟩ := frameName
      refine ⟨name, afterCnf, opened, named, cnf, opening, consumed, nameValid, fresh, ?_, ?_, tail⟩
      · simp only [nameState, openingState, cnfState]
      · simp only [nameState, openingState, cnfState]

theorem StatementTailRun.clause_names {fuel : Nat} {state final : State} {clause : Clause}
    (success : StatementTailRun fuel state clause final) :
    final.clauseNames = state.clauseNames := by
  let property : List String → Prop := fun names => names = state.clauseNames
  have preserved : PreservesClauseProperty property (do
    expect ","
    if (← peek) != some "axiom" then fail "unsupported: only the axiom role is supported"
    expect "axiom"
    expect ","
    expect "("
    let body ← if (← peek) == some "$false" then expect "$false"; pure []
      else literals fuel
    expect ")"
    expect ")"
    expect "."
    pure body) := by
      apply clauseProperty_bind (clauseProperty_expect property ",")
      intro ignored
      apply clauseProperty_bind (clauseProperty_peek property)
      intro next
      split
      · exact clauseProperty_fail_bind property _ _
      · apply clauseProperty_bind (clauseProperty_expect property "axiom")
        intro ignored
        apply clauseProperty_bind (clauseProperty_expect property ",")
        intro ignored
        apply clauseProperty_bind (clauseProperty_expect property "(")
        intro ignored
        apply clauseProperty_bind (clauseProperty_peek property)
        intro next
        split
        · apply clauseProperty_bind (clauseProperty_expect property "$false")
          intro ignored
          apply clauseProperty_bind (clauseProperty_pure property [])
          intro body
          apply clauseProperty_bind (clauseProperty_expect property ")")
          intro ignored
          apply clauseProperty_bind (clauseProperty_expect property ")")
          intro ignored
          exact clauseProperty_bind (clauseProperty_expect property ".") (fun _ => clauseProperty_pure property _)
        · apply clauseProperty_bind (clauseProperty_literals property fuel)
          intro body
          apply clauseProperty_bind (clauseProperty_expect property ")")
          intro ignored
          apply clauseProperty_bind (clauseProperty_expect property ")")
          intro ignored
          exact clauseProperty_bind (clauseProperty_expect property ".") (fun _ => clauseProperty_pure property _)
  exact preserved state clause final rfl success

theorem statement_name_history {fuel : Nat} {state final : State} {clause : Clause}
    (success : statement fuel state = .ok (clause, final)) :
    ∃ name, name ∉ state.clauseNames ∧ final.clauseNames = state.clauseNames ++ [name] := by
  obtain ⟨name, _, _, named, _, _, _, _, fresh, names, _, tail⟩ :=
    statement_success_decomposition success
  refine ⟨name, by simpa only [names] using fresh, ?_⟩
  simpa only [names] using tail.clause_names

#print axioms literals_preserve_clause_names
#print axioms statement_preserves_unique_clause_names
#print axioms statements_preserve_unique_clause_names
#print axioms clause_update_success_iff
#print axioms statement_success_decomposition
#print axioms StatementTailRun.clause_names
#print axioms statement_name_history

end Fang.Frontend
