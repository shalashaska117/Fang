/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFGroundComplete

namespace Fang.FOFFrontend
open Frontend FOFGrammar

def RawDisjunctionCompletion (signature : Source.Signature) (state : State)
    (named : List Source.Literal) (rest : List String) : Prop :=
  ∃ fuel encoded updated, Frontend.literals fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ spellings updated = ")" :: rest ∧
    TableClauseEncoding updated named encoded ∧ TableExtension state updated

theorem raw_disjunction_complete {input named rest} (parsed : DisjunctionTokens input named rest)
    (signature : Source.Signature) (state : State) (words : spellings state = input)
    (wellFormed : ∀ literal ∈ named, literal.WellFormed signature)
    (compatible : SignatureCompatible signature state) :
    RawDisjunctionCompletion signature state named rest := by
  induction parsed generalizing state with
  | last head =>
    obtain ⟨fuel, first, final, firstRun, finalCompatible, finalWords, firstEncoding, extension⟩ :=
      raw_literal_complete head signature state words (wellFormed _ List.mem_cons_self) compatible
    have noDisjoin : final.tokens.head?.map Token.text ≠ some "|" := by
      rw [← spellings_head, finalWords]
      simp
    refine ⟨fuel + 1, [first], final, ?_, finalCompatible, finalWords,
      .cons firstEncoding .nil, extension⟩
    rw [literals_run]
    simp [firstRun, noDisjoin, bind, Except.bind]
  | more head tail ih =>
    obtain ⟨firstFuel, first, afterFirst, firstRun, firstCompatible, firstWords, firstEncoding, firstExtension⟩ :=
      raw_literal_complete head signature state words (wellFormed _ List.mem_cons_self) compatible
    obtain ⟨afterDisjoin, disjoinRun, disjoinWords, disjoinExtension, functions, predicates⟩ :=
      raw_expect_complete firstWords
    obtain ⟨tailFuel, args, final, tailRun, finalCompatible, finalWords, tailEncoding, tailExtension⟩ :=
      ih afterDisjoin disjoinWords
        (fun item member => wellFormed item (List.mem_cons_of_mem _ member))
        (firstCompatible.same_tables functions predicates)
    let fuel := max firstFuel tailFuel
    have firstRun' := literal_fuel_monotone firstFuel fuel (Nat.le_max_left _ _) state first afterFirst firstRun
    have tailRun' := literals_fuel_monotone tailFuel fuel (Nat.le_max_right _ _) afterDisjoin args final tailRun
    have hasDisjoin : afterFirst.tokens.head?.map Token.text = some "|" := by
      rw [← spellings_head, firstWords]; rfl
    have extension := disjoinExtension.trans tailExtension
    refine ⟨fuel + 1, first :: args, final, ?_, finalCompatible, finalWords,
      .cons (firstEncoding.extend extension) tailEncoding, firstExtension.trans extension⟩
    rw [literals_run]
    simp [firstRun', hasDisjoin, disjoinRun, tailRun', bind, Except.bind, pure, Except.pure]

theorem raw_cnf_closing_complete {signature state rest}
    (words : spellings state = ")" :: ")" :: "." :: rest)
    (compatible : SignatureCompatible signature state) (body : Clause) :
    ∃ updated, StatementClosingRun body state updated body ∧ SignatureCompatible signature updated := by
  obtain ⟨first, firstRun, firstWords, _, firstFunctions, firstPredicates⟩ := raw_expect_complete words
  obtain ⟨second, secondRun, secondWords, _, secondFunctions, secondPredicates⟩ := raw_expect_complete firstWords
  obtain ⟨final, finalRun, _, _, finalFunctions, finalPredicates⟩ := raw_expect_complete secondWords
  refine ⟨final, ?_, ((compatible.same_tables firstFunctions firstPredicates).same_tables
    secondFunctions secondPredicates).same_tables finalFunctions finalPredicates⟩
  simp [StatementClosingRun, bind, StateT.bind, firstRun, secondRun, finalRun,
    Except.bind, pure, StateT.pure, Except.pure]

theorem raw_cnf_body_complete {input named rest}
    (parsed : BodyTokens input named rest) (signature : Source.Signature) (state : State)
    (words : spellings state = input)
    (wellFormed : ∀ literal ∈ named, literal.WellFormed signature)
    (compatible : SignatureCompatible signature state) :
    ∃ fuel body updated,
      ((do
        if (← peek) == some "$false" then
          expect "$false"
          pure []
        else Frontend.literals fuel : Parser Clause) state) = .ok (body, updated) ∧
      SignatureCompatible signature updated ∧ spellings updated = ")" :: rest := by
  cases parsed with
  | falsity rest =>
    obtain ⟨updated, falseRun, finalWords, _, functions, predicates⟩ := raw_expect_complete words
    have hasFalse : state.tokens.head?.map Token.text = some "$false" := by
      rw [← spellings_head, words]; rfl
    refine ⟨0, [], updated, ?_, compatible.same_tables functions predicates, finalWords⟩
    simp [bind, StateT.bind, peek_run, hasFalse, falseRun, Except.bind, pure, StateT.pure, Except.pure]
  | disjunction body =>
    obtain ⟨fuel, encoded, updated, success, finalCompatible, finalWords, _, _⟩ :=
      raw_disjunction_complete body signature state words wellFormed compatible
    have noFalse : state.tokens.head?.map Token.text ≠ some "$false" := by
      rw [← spellings_head, words]
      exact body.not_false
    refine ⟨fuel, encoded, updated, ?_, finalCompatible, finalWords⟩
    simp [bind, StateT.bind, peek_run, noFalse, success, Except.bind]

theorem raw_cnf_tail_complete {input named rest}
    (parsed : BodyTokens input named (")" :: "." :: rest))
    (signature : Source.Signature) (state : State)
    (words : spellings state = "," :: "axiom" :: "," :: "(" :: input)
    (wellFormed : ∀ literal ∈ named, literal.WellFormed signature)
    (compatible : SignatureCompatible signature state) :
    ∃ fuel encoded updated, StatementTailRun fuel state encoded updated ∧
      SignatureCompatible signature updated := by
  obtain ⟨afterComma, commaRun, commaWords, _, commaFunctions, commaPredicates⟩ := raw_expect_complete words
  obtain ⟨afterRole, roleRun, roleWords, _, roleFunctions, rolePredicates⟩ := raw_expect_complete commaWords
  obtain ⟨nextComma, nextRun, nextWords, _, nextFunctions, nextPredicates⟩ := raw_expect_complete roleWords
  obtain ⟨opened, openRun, openWords, _, openFunctions, openPredicates⟩ := raw_expect_complete nextWords
  have openedCompatible := (((compatible.same_tables commaFunctions commaPredicates).same_tables
    roleFunctions rolePredicates).same_tables nextFunctions nextPredicates).same_tables openFunctions openPredicates
  obtain ⟨fuel, body, afterBody, bodyRun, bodyCompatible, bodyWords⟩ :=
    raw_cnf_body_complete parsed signature opened openWords wellFormed openedCompatible
  obtain ⟨updated, closingRun, finalCompatible⟩ := raw_cnf_closing_complete bodyWords bodyCompatible body
  refine ⟨fuel, body, updated, ?_, finalCompatible⟩
  have roleText : afterComma.tokens.head?.map Token.text = some "axiom" := by
    rw [← spellings_head, commaWords]; rfl
  unfold StatementTailRun
  simp only [bind, StateT.bind, commaRun, Except.bind, peek_run, roleText,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure,
    roleRun, nextRun, openRun]
  have combined : ((do
    let body ← (do
      if (← peek) == some "$false" then
        expect "$false"
        pure []
      else Frontend.literals fuel : Parser Clause)
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

theorem raw_cnf_declaration_complete {input named rest}
    (parsed : CNFDeclarationTokens input named rest)
    (signature : Source.Signature) (state : State) (words : spellings state = input)
    (wellFormed : named.WellFormed signature) (compatible : SignatureCompatible signature state)
    (fresh : named.name ∉ state.clauseNames) :
    RawDeclarationCompletion signature state (.cnf named) rest := by
  have runs : ∃ fuel encoded updated, Frontend.statement fuel state = .ok (encoded, updated) ∧
      SignatureCompatible signature updated := by
    cases parsed with
    | «axiom» valid body =>
      have hasCnf : state.tokens.head?.map Token.text = some "cnf" := by
        rw [← spellings_head, words]; rfl
      obtain ⟨afterCnf, cnfRun, cnfWords, _, cnfFunctions, cnfPredicates⟩ := raw_expect_complete words
      obtain ⟨opened, openRun, openWords, _, openFunctions, openPredicates⟩ := raw_expect_complete cnfWords
      obtain ⟨raw, raws, shape, text, tail⟩ := spellings_cons_parts openWords
      let namedState : State := { opened with tokens := raws }
      let reset : State := { namedState with clauseNames := namedState.clauseNames ++ [raw.text], variables := [] }
      have resetWords : spellings reset = _ := tail
      have resetCompatible : SignatureCompatible signature reset :=
        (compatible.same_tables cnfFunctions cnfPredicates).same_tables openFunctions openPredicates
      obtain ⟨fuel, encoded, updated, tailRun, finalCompatible⟩ :=
        raw_cnf_tail_complete body signature reset resetWords wellFormed resetCompatible
      have names : namedState.clauseNames = state.clauseNames := by
        dsimp [namedState]
        exact (expect_clause_names openRun).trans (expect_clause_names cnfRun)
      have nameRun : consume opened = .ok (raw.text, namedState) := consume_cons opened raw raws shape
      exact ⟨fuel, encoded, updated, Frontend.statement_success_of_parts hasCnf cnfRun openRun nameRun
        (by simpa only [text] using (raw_lower_valid valid).1)
        (by simpa only [names, text] using fresh) tailRun, finalCompatible⟩
  obtain ⟨fuel, encoded, updated, success, finalCompatible⟩ := runs
  obtain ⟨actual, encoding, extension, grammar, _, names⟩ := raw_cnf_statement_grammar success
  rw [words] at grammar
  obtain ⟨rfl, restEqual⟩ := parsed.unique grammar
  have hasCnf : (state.tokens.head?.map Token.text == some "cnf") = true := by
    cases parsed
    rw [← spellings_head, words]
    rfl
  refine ⟨fuel, .cnf encoded, updated, ?_, finalCompatible, restEqual.symm, encoding, extension, names⟩
  rw [statement_cnf_run fuel state hasCnf, success]
  rfl

end Fang.FOFFrontend
