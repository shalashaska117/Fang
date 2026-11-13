/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFTermGrammar
import Fang.FOF.FOFCNFEncoding

namespace Fang.FOFGrammar

inductive LiteralTokens : List String → Source.Literal → List String → Prop where
  | positive {input rest name arguments} (atom : TermTokens input (.app name arguments) rest) :
      LiteralTokens input ⟨true, name, arguments⟩ rest
  | negative {input rest name arguments} (atom : TermTokens input (.app name arguments) rest) :
      LiteralTokens ("~" :: input) ⟨false, name, arguments⟩ rest

inductive DisjunctionPrefix : List String → List Source.Literal → List String → Prop where
  | last {input rest literal} (head : LiteralTokens input literal rest)
      (noDisjoin : rest.head? ≠ some "|") : DisjunctionPrefix input [literal] rest
  | more {input middle rest literal literals} (head : LiteralTokens input literal ("|" :: middle))
      (tail : DisjunctionPrefix middle literals rest) : DisjunctionPrefix input (literal :: literals) rest

inductive DisjunctionTokens : List String → List Source.Literal → List String → Prop where
  | last {input rest literal} (head : LiteralTokens input literal (")" :: rest)) :
      DisjunctionTokens input [literal] rest
  | more {input middle rest literal literals} (head : LiteralTokens input literal ("|" :: middle))
      (tail : DisjunctionTokens middle literals rest) : DisjunctionTokens input (literal :: literals) rest

theorem DisjunctionPrefix.body {input literals rest}
    (parsed : DisjunctionPrefix input literals (")" :: rest)) : DisjunctionTokens input literals rest := by
  generalize ending : ")" :: rest = output at parsed
  induction parsed with
  | last head noDisjoin => exact .last (ending ▸ head)
  | more head tail ih => exact .more head (ih ending)

inductive BodyTokens : List String → List Source.Literal → List String → Prop where
  | falsity (rest) : BodyTokens ("$false" :: ")" :: rest) [] rest
  | disjunction {input literals rest} (body : DisjunctionTokens input literals rest) :
      BodyTokens input literals rest

inductive CNFDeclarationTokens : List String → Source.Clause → List String → Prop where
  | axiom {name input rest literals} (valid : Source.Grammar.LowerName name)
      (body : BodyTokens input literals (")" :: "." :: rest)) :
      CNFDeclarationTokens ("cnf" :: "(" :: name :: "," :: "axiom" :: "," :: "(" :: input)
        ⟨name, literals⟩ rest

end Fang.FOFGrammar

namespace Fang.FOFFrontend
open Frontend

theorem raw_literal_grammar {fuel state encoded updated}
    (success : literal fuel state = .ok (encoded, updated)) :
    ∃ named, TableLiteralEncoding updated named encoded ∧ TableExtension state updated ∧
      FOFGrammar.LiteralTokens (spellings state) named (spellings updated) := by
  rw [literal_run] at success
  cases prefixRun : (if state.tokens.head?.map Token.text == some "~" then do
      let (_, final) ← expect "~" state
      pure (false, final)
    else .ok (true, state)) with
  | error error => rw [prefixRun] at success; simp [Except.bind] at success
  | ok pair =>
      rcases pair with ⟨positive, beforeName⟩
      rw [prefixRun] at success
      simp only [Except.bind] at success
      have prefixContract : TableExtension state beforeName ∧
          ∀ name args rest, FOFGrammar.TermTokens (spellings beforeName) (.app name args) rest →
            FOFGrammar.LiteralTokens (spellings state) ⟨positive, name, args⟩ rest := by
        split at prefixRun
        · cases negated : expect "~" state with
          | error error => simp [negated, bind, Except.bind] at prefixRun
          | ok pair =>
              rcases pair with ⟨ignored, final⟩
              cases ignored
              simp [negated, bind, Except.bind, pure, Except.pure] at prefixRun
              rcases prefixRun with ⟨rfl, rfl⟩
              refine ⟨expect_tableExtension negated, ?_⟩
              intro name args rest grammar
              rw [expect_spellings negated]
              exact .negative grammar
        · cases prefixRun
          exact ⟨.refl state, fun _ _ _ grammar => .positive grammar⟩
      cases consumedRun : consume beforeName with
      | error error => simp [consumedRun, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨name, consumed⟩
          simp only [consumedRun, bind, Except.bind] at success
          cases valid : lowerName name with
          | false => simp [valid, failAt_run] at success
          | true =>
              simp only [valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success
              obtain ⟨id, reserved, allocated, allocation, reservedTokens, _⟩ := reserveSymbol_spec true name consumed
              simp only [allocated] at success
              cases argsRun : (if reserved.tokens.head?.map Token.text == some "(" then do
                  let (_, opened) ← expect "(" reserved
                  let (args, afterArgs) ← terms fuel opened
                  let (_, closed) ← expect ")" afterArgs
                  pure (args, closed)
                else .ok ([], reserved)) with
              | error error =>
                  simp only [bind, Except.bind] at argsRun
                  rw [argsRun] at success
                  simp at success
              | ok pair =>
                  rcases pair with ⟨args, afterArgs⟩
                  simp only [bind, Except.bind] at argsRun
                  rw [argsRun] at success
                  simp only at success
                  cases arityRun : checkArity true id args.length
                      ((beforeName.tokens.head?.map Token.offset).getD beforeName.endOffset) afterArgs with
                  | error error => simp [arityRun] at success
                  | ok pair =>
                      rcases pair with ⟨ignored, final⟩
                      cases ignored
                      simp [arityRun, pure, Except.pure] at success
                      rcases success with ⟨rfl, rfl⟩
                      obtain ⟨namedArgs, argsEncoding, argsExtension, grammar⟩ :=
                        raw_function_arguments fuel reserved name
                          ((lowerName_iff _ (lowerName_ascii valid)).mp valid)
                          (fun success => raw_terms_grammar success) argsRun
                      have arityExtension := checkArity_tableExtension true id args.length _ afterArgs final arityRun
                      have allocatedExtension := reserveSymbol_tableExtension true name consumed reserved id allocated
                      have contract := checkArity_success true id args.length _ afterArgs final arityRun
                      have reservedId : symbolIndex name reserved.predicates 0 = some id := by
                        rw [symbolIndex_eq_namedIndex]
                        exact (namedIndex_first_iff _ _ _).mpr allocation.1
                      have finalId := arityExtension.symbols true name id (argsExtension.symbols true name id reservedId)
                      have namedArity : (final.predicates[id]?).map Symbol.arity = some (some namedArgs.length) := by
                        simpa only [argsEncoding.length, symbolTable, ↓reduceIte] using contract.1
                      refine ⟨⟨positive, name, namedArgs⟩,
                        ⟨rfl, finalId, namedArity, argsEncoding.extend arityExtension⟩,
                        prefixContract.1.trans ((consume_tableExtension consumedRun).trans
                          (allocatedExtension.trans (argsExtension.trans arityExtension))), ?_⟩
                      apply prefixContract.2
                      rw [consume_spellings consumedRun]
                      simpa only [spellings, reservedTokens, contract.2.2.1] using grammar

theorem raw_cnf_literals_grammar {fuel state encoded updated}
    (success : Frontend.literals fuel state = .ok (encoded, updated)) :
    ∃ named, TableClauseEncoding updated named encoded ∧ TableExtension state updated ∧
      FOFGrammar.DisjunctionPrefix (spellings state) named (spellings updated) := by
  induction fuel generalizing state encoded updated with
  | zero => simp [Frontend.literals, fail_run] at success
  | succ fuel ih =>
      rw [literals_run] at success
      cases firstRun : literal fuel state with
      | error error => simp [firstRun, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨first, afterFirst⟩
          simp only [firstRun, bind, Except.bind] at success
          obtain ⟨namedFirst, firstEncoding, firstExtension, firstGrammar⟩ := raw_literal_grammar firstRun
          split at success
          · cases disjoinRun : expect "|" afterFirst with
            | error error => simp [disjoinRun] at success
            | ok pair =>
                rcases pair with ⟨ignored, afterDisjoin⟩
                cases ignored
                cases tailRun : Frontend.literals fuel afterDisjoin with
                | error error => simp [disjoinRun, tailRun] at success
                | ok pair =>
                    rcases pair with ⟨tail, final⟩
                    simp [disjoinRun, tailRun, pure, Except.pure] at success
                    rcases success with ⟨rfl, rfl⟩
                    obtain ⟨namedTail, tailEncoding, tailExtension, tailGrammar⟩ := ih tailRun
                    have extension := (expect_tableExtension disjoinRun).trans tailExtension
                    rw [expect_spellings disjoinRun] at firstGrammar
                    exact ⟨namedFirst :: namedTail, .cons (firstEncoding.extend extension) tailEncoding,
                      firstExtension.trans extension, .more firstGrammar tailGrammar⟩
          · rename_i noDisjoin
            cases success
            have absent : (spellings updated).head? ≠ some "|" := by
              rw [spellings_head]
              simpa only [beq_iff_eq] using noDisjoin
            exact ⟨[namedFirst], .cons firstEncoding .nil, firstExtension, .last firstGrammar absent⟩

theorem raw_cnf_closing_grammar {body : Clause} {state updated : State} {encoded : Clause}
    (success : (do
      expect ")"
      expect ")"
      expect "."
      pure body : Parser Clause) state = .ok (encoded, updated)) :
    encoded = body ∧ TableExtension state updated ∧
      spellings state = ")" :: ")" :: "." :: spellings updated := by
  obtain ⟨ignored, first, firstRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨ignored, second, secondRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨ignored, final, periodRun, success⟩ := parser_bind_success success
  cases ignored
  cases Except.ok.inj success
  exact ⟨rfl, (expect_tableExtension firstRun).trans
    ((expect_tableExtension secondRun).trans (expect_tableExtension periodRun)),
    by rw [expect_spellings firstRun, expect_spellings secondRun, expect_spellings periodRun]⟩

theorem raw_cnf_tail_grammar {fuel state encoded updated}
    (success : StatementTailRun fuel state encoded updated) :
    ∃ named bodyInput,
      spellings state = "," :: "axiom" :: "," :: "(" :: bodyInput ∧
      FOFGrammar.BodyTokens bodyInput named (")" :: "." :: spellings updated) ∧
      TableClauseEncoding updated named encoded ∧ TableExtension state updated := by
  unfold StatementTailRun at success
  obtain ⟨ignored, afterComma, commaRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨role, roleState, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  split at success
  · simp [bind, StateT.bind, fail_run, Except.bind] at success
  · obtain ⟨ignored, afterRole, roleRun, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨ignored, nextComma, nextCommaRun, success⟩ := parser_bind_success success
    cases ignored
    obtain ⟨ignored, opened, openingRun, success⟩ := parser_bind_success success
    cases ignored
    have headerShape : spellings state = "," :: "axiom" :: "," :: "(" :: spellings opened := by
      rw [expect_spellings commaRun, expect_spellings roleRun, expect_spellings nextCommaRun,
        expect_spellings openingRun]
    have headerExtension := (expect_tableExtension commaRun).trans
      ((expect_tableExtension roleRun).trans ((expect_tableExtension nextCommaRun).trans
        (expect_tableExtension openingRun)))
    obtain ⟨next, peekState, peeked, success⟩ := parser_bind_success success
    rw [peek_run] at peeked
    cases peeked
    split at success
    · obtain ⟨ignored, afterFalse, falseRun, success⟩ := parser_bind_success success
      cases ignored
      obtain ⟨body, bodyState, returned, success⟩ := parser_bind_success success
      have same : (([] : Clause), afterFalse) = (body, bodyState) := Except.ok.inj returned
      cases same
      obtain ⟨rfl, closingExtension, closingShape⟩ := raw_cnf_closing_grammar success
      refine ⟨[], spellings opened, headerShape, ?_, .nil,
        headerExtension.trans ((expect_tableExtension falseRun).trans closingExtension)⟩
      rw [expect_spellings falseRun, closingShape]
      exact .falsity _
    · obtain ⟨body, afterBody, bodyRun, success⟩ := parser_bind_success success
      obtain ⟨named, encoding, bodyExtension, bodyGrammar⟩ := raw_cnf_literals_grammar bodyRun
      obtain ⟨rfl, closingExtension, closingShape⟩ := raw_cnf_closing_grammar success
      rw [closingShape] at bodyGrammar
      exact ⟨named, spellings opened, headerShape, .disjunction bodyGrammar.body,
        encoding.extend closingExtension, headerExtension.trans (bodyExtension.trans closingExtension)⟩

theorem raw_cnf_statement_grammar {fuel state encoded updated}
    (success : Frontend.statement fuel state = .ok (encoded, updated)) :
    ∃ named, TableDeclarationEncoding updated (.cnf named) (.cnf encoded) ∧
      SymbolExtension state updated ∧
      FOFGrammar.CNFDeclarationTokens (spellings state) named (spellings updated) ∧
      named.name ∉ state.clauseNames ∧ updated.clauseNames = state.clauseNames ++ [named.name] := by
  obtain ⟨name, afterCnf, opened, namedState, cnfRun, openingRun, nameRun, valid,
    fresh, priorNames, priorVariables, tailRun⟩ := statement_success_decomposition success
  obtain ⟨named, bodyInput, tailShape, bodyGrammar, encoding, tailExtension⟩ := raw_cnf_tail_grammar tailRun
  have headerExtension := (expect_tableExtension cnfRun).trans
    ((expect_tableExtension openingRun).trans (consume_tableExtension nameRun))
  refine ⟨⟨name, named⟩, .cnf updated.variables name encoding,
    headerExtension.toSymbolExtension.trans
      ((symbolExtension_reset namedState [] (namedState.clauseNames ++ [name])).trans
        tailExtension.toSymbolExtension), ?_,
    by simpa only [priorNames] using fresh,
    by simpa only [priorNames] using tailRun.clause_names⟩
  rw [expect_spellings cnfRun, expect_spellings openingRun, consume_spellings nameRun]
  change spellings namedState = _ at tailShape
  rw [tailShape]
  exact .axiom ((lowerName_iff _ (lowerName_ascii valid)).mp valid) bodyGrammar

end Fang.FOFFrontend
