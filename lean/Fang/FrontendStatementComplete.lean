/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Converse acceptance for complete clauses, including the exact clause-local
variable reset and source-name freshness check of the existing decoder.
-/
import Fang.FrontendLiteralComplete
import Fang.FrontendStatementGrammar

namespace Fang.Frontend

open Source.Grammar

theorem parser_bind_of_success {α β : Type} {head : Parser α} {tail : α → Parser β}
    {state middle final : State} {value : α} {result : β}
    (first : head state = .ok (value, middle))
    (second : tail value middle = .ok (result, final)) :
    (head >>= tail) state = .ok (result, final) := by
  change Except.bind (head state) (fun pair => tail pair.1 pair.2) = _
  rw [first]
  exact second

theorem ClassifiedTokens.head_text {state : State} {token : Source.Grammar.Token} {rest}
    (classified : ClassifiedTokens state.tokens (token :: rest)) :
    state.tokens.head?.map Token.text = some token.text := by
  obtain ⟨raw, raws, shape, head, _⟩ := classified.cons_parts
  simp only [shape, List.head?_cons, Option.map_some, head.text]

theorem statement_closing_complete {signature state rest}
    (classified : ClassifiedTokens state.tokens (.rparen :: .rparen :: .period :: rest))
    (compatible : SignatureCompatible signature state) (body : Clause) :
    ∃ updated, StatementClosingRun body state updated body ∧ SignatureCompatible signature updated := by
  obtain ⟨first, firstRun, firstClass, _, firstFunctions, firstPredicates⟩ := expect_complete classified
  obtain ⟨second, secondRun, secondClass, _, secondFunctions, secondPredicates⟩ := expect_complete firstClass
  obtain ⟨final, finalRun, _, _, finalFunctions, finalPredicates⟩ := expect_complete secondClass
  refine ⟨final, ?_, ((compatible.same_tables firstFunctions firstPredicates).same_tables
    secondFunctions secondPredicates).same_tables finalFunctions finalPredicates⟩
  change expect ")" state = .ok ((), first) at firstRun
  change expect ")" first = .ok ((), second) at secondRun
  change expect "." second = .ok ((), final) at finalRun
  simp [StatementClosingRun, bind, StateT.bind, firstRun, secondRun, finalRun,
    Except.bind, pure, StateT.pure, Except.pure]

theorem statement_body_complete {input named rest}
    (parsed : BodyTokens input named rest) (signature : Source.Signature) (state : State)
    (classified : ClassifiedTokens state.tokens input)
    (wellFormed : ∀ literal ∈ named, literal.WellFormed signature)
    (compatible : SignatureCompatible signature state) :
    ∃ fuel body updated,
      ((do
        if (← peek) == some "$false" then
          expect "$false"
          pure []
        else literals fuel : Parser Clause) state) = .ok (body, updated) ∧
      SignatureCompatible signature updated ∧
      ClassifiedTokens updated.tokens (.rparen :: rest) := by
  cases parsed with
  | falsity rest =>
    obtain ⟨updated, falseRun, finalClass, _, functions, predicates⟩ := expect_complete classified
    have hasFalse : state.tokens.head?.map Token.text = some "$false" := classified.head_text
    change expect "$false" state = .ok ((), updated) at falseRun
    refine ⟨0, [], updated, ?_, compatible.same_tables functions predicates, finalClass⟩
    simp [bind, StateT.bind, peek_run, hasFalse, falseRun, Except.bind, pure, StateT.pure, Except.pure]
  | disjunction body =>
    obtain ⟨fuel, encoded, updated, success, finalCompatible, finalClass, _, _⟩ :=
      disjunction_complete body signature state classified wellFormed compatible
    have noFalse : state.tokens.head?.map Token.text ≠ some "$false" := by
      intro same
      cases shape : state.tokens with
      | nil => simp [shape] at same
      | cons raw raws =>
        simp only [shape, List.head?_cons, Option.map_some, Option.some.injEq] at same
        rw [shape] at classified
        cases classified with
        | cons head tail =>
          have token := head.unique (rawTokenSpelling_false raw same)
          exact body.not_false (by simp only [List.head?_cons, token])
    refine ⟨fuel, encoded, updated, ?_, finalCompatible, finalClass⟩
    simp [bind, StateT.bind, peek_run, noFalse, success, Except.bind]

theorem statement_tail_complete {input named rest}
    (parsed : BodyTokens input named (.rparen :: .period :: rest))
    (signature : Source.Signature) (state : State)
    (classified : ClassifiedTokens state.tokens (.comma :: .lower "axiom" :: .comma :: .lparen :: input))
    (wellFormed : ∀ literal ∈ named, literal.WellFormed signature)
    (compatible : SignatureCompatible signature state) :
    ∃ fuel encoded updated, StatementTailRun fuel state encoded updated ∧
      SignatureCompatible signature updated := by
  obtain ⟨afterComma, commaRun, commaClass, _, commaFunctions, commaPredicates⟩ := expect_complete classified
  obtain ⟨afterRole, roleRun, roleClass, _, roleFunctions, rolePredicates⟩ := expect_complete commaClass
  obtain ⟨nextComma, nextRun, nextClass, _, nextFunctions, nextPredicates⟩ := expect_complete roleClass
  obtain ⟨opened, openRun, openClass, _, openFunctions, openPredicates⟩ := expect_complete nextClass
  have openedCompatible := (((compatible.same_tables commaFunctions commaPredicates).same_tables
    roleFunctions rolePredicates).same_tables nextFunctions nextPredicates).same_tables openFunctions openPredicates
  obtain ⟨fuel, body, afterBody, bodyRun, bodyCompatible, bodyClass⟩ :=
    statement_body_complete parsed signature opened openClass wellFormed openedCompatible
  obtain ⟨updated, closingRun, finalCompatible⟩ := statement_closing_complete bodyClass bodyCompatible body
  refine ⟨fuel, body, updated, ?_, finalCompatible⟩
  have roleText : afterComma.tokens.head?.map Token.text = some "axiom" := commaClass.head_text
  change expect "," state = .ok ((), afterComma) at commaRun
  change expect "axiom" afterComma = .ok ((), afterRole) at roleRun
  change expect "," afterRole = .ok ((), nextComma) at nextRun
  change expect "(" nextComma = .ok ((), opened) at openRun
  unfold StatementTailRun
  simp only [bind, StateT.bind, commaRun, Except.bind, peek_run, roleText,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure,
    roleRun, nextRun, openRun]
  have combined : ((do
    let body ← (do
      if (← peek) == some "$false" then
        expect "$false"
        pure []
      else literals fuel : Parser Clause)
    expect ")"
    expect ")"
    expect "."
    pure body : Parser Clause) opened) = .ok (body, updated) := by
      exact parser_bind_of_success bodyRun closingRun
  by_cases selected : opened.tokens.head?.map Token.text == some "$false"
  · cases falseRun : expect "$false" opened with
    | error error =>
      simp [bind, StateT.bind, peek_run, Except.bind, selected, falseRun] at combined
    | ok pair =>
      simpa [bind, StateT.bind, peek_run, Except.bind, selected, falseRun,
        pure, StateT.pure, Except.pure] using combined
  · simpa [bind, StateT.bind, peek_run, Except.bind, selected,
      pure, StateT.pure, Except.pure] using combined

theorem statement_success_of_parts {fuel state afterCnf opened namedState final clause name}
    (hasCnf : state.tokens.head?.map Token.text = some "cnf")
    (cnfRun : expect "cnf" state = .ok ((), afterCnf))
    (openRun : expect "(" afterCnf = .ok ((), opened))
    (nameRun : consume opened = .ok (name, namedState))
    (valid : lowerName name = true) (fresh : name ∉ namedState.clauseNames)
    (tailRun : StatementTailRun fuel
      { namedState with clauseNames := namedState.clauseNames ++ [name], variables := [] } clause final) :
    statement fuel state = .ok (clause, final) := by
  simp only [statement, bind, StateT.bind, peek_run, hasCnf, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, pure, Except.bind,
    cnfRun, openRun, position_run, nameRun, valid, Bool.not_true]
  simpa only [StatementTailRun, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    List.contains_eq_mem, fresh, decide_false, Bool.false_eq_true, ↓reduceIte, set, StateT.set, Except.bind,
    pure, StateT.pure, Except.pure] using tailRun

def StatementCompletion (signature : Source.Signature) (state : State)
    (named : Source.Clause) (rest : List Source.Grammar.Token) : Prop :=
  ∃ fuel encoded updated, statement fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ ClassifiedTokens updated.tokens rest ∧
    TableClauseEncoding updated named.literals encoded ∧ SymbolExtension state updated ∧
    updated.clauseNames = state.clauseNames ++ [named.name]

theorem statement_complete {input named rest} (parsed : StatementTokens input named rest)
    (signature : Source.Signature) (state : State)
    (classified : ClassifiedTokens state.tokens input)
    (wellFormed : named.WellFormed signature) (compatible : SignatureCompatible signature state)
    (fresh : named.name ∉ state.clauseNames) : StatementCompletion signature state named rest := by
  have runs : ∃ fuel encoded updated, statement fuel state = .ok (encoded, updated) ∧
      SignatureCompatible signature updated := by
    cases parsed with
    | statement name body =>
      have hasCnf : state.tokens.head?.map Token.text = some "cnf" := classified.head_text
      obtain ⟨afterCnf, cnfRun, cnfClass, _, cnfFunctions, cnfPredicates⟩ := expect_complete classified
      obtain ⟨opened, openRun, openClass, _, openFunctions, openPredicates⟩ := expect_complete cnfClass
      obtain ⟨raw, raws, shape, head, remaining⟩ := openClass.cons_parts
      have valid := head.lower_valid
      let namedState : State := { opened with tokens := raws }
      let reset : State := { namedState with clauseNames := namedState.clauseNames ++ [name], variables := [] }
      have resetClass : ClassifiedTokens reset.tokens _ := remaining
      have resetCompatible : SignatureCompatible signature reset :=
        (compatible.same_tables cnfFunctions cnfPredicates).same_tables openFunctions openPredicates
      obtain ⟨fuel, encoded, updated, tailRun, finalCompatible⟩ :=
        statement_tail_complete body signature reset resetClass wellFormed resetCompatible
      have names : namedState.clauseNames = state.clauseNames := by
        obtain ⟨_, _, _, _, cnfShape⟩ := expect_success cnfRun
        obtain ⟨_, _, _, _, openShape⟩ := expect_success openRun
        simp only [namedState, openShape, cnfShape]
      have nameRun : consume opened = .ok (name, namedState) := by
        simpa only [valid.1] using consume_cons opened raw raws shape
      refine ⟨fuel, encoded, updated, ?_, finalCompatible⟩
      exact statement_success_of_parts hasCnf cnfRun openRun nameRun (valid.1 ▸ valid.2.1)
        (by simpa only [names] using fresh) tailRun
  obtain ⟨fuel, encoded, updated, success, finalCompatible⟩ := runs
  obtain ⟨actual, ending, encoding, extension, grammar, remaining, _, names⟩ := statement_grammar classified success
  obtain ⟨rfl, rfl⟩ := parsed.unique grammar
  exact ⟨fuel, encoded, updated, success, finalCompatible, remaining, encoding, extension, names⟩

end Fang.Frontend

#print axioms Fang.Frontend.statement_tail_complete
#print axioms Fang.Frontend.statement_complete
