/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFDeclarationEncoding

namespace Fang.FOFFrontend
open Frontend

theorem cnf_literals_result {fuel state encoded updated}
    (success : Frontend.literals fuel state = .ok (encoded, updated)) :
    ∃ named, TableClauseEncoding updated named encoded ∧ TableExtension state updated := by
  induction fuel generalizing state encoded updated with
  | zero => simp [Frontend.literals, fail_run] at success
  | succ fuel ih =>
      rw [literals_run] at success
      cases firstRun : literal fuel state with
      | error error => simp [firstRun, bind, Except.bind] at success
      | ok pair =>
          rcases pair with ⟨first, afterFirst⟩
          simp only [firstRun, bind, Except.bind] at success
          obtain ⟨namedFirst, firstEncoding, firstExtension⟩ := literal_result firstRun
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
                    obtain ⟨namedTail, tailEncoding, tailExtension⟩ := ih tailRun
                    have extension := (expect_tableExtension disjoinRun).trans tailExtension
                    exact ⟨namedFirst :: namedTail, .cons (firstEncoding.extend extension) tailEncoding,
                      firstExtension.trans extension⟩
          · cases success
            exact ⟨[namedFirst], .cons firstEncoding .nil, firstExtension⟩

theorem cnf_closing_result {body : Clause} {state updated : State} {encoded : Clause}
    (success : (do
      expect ")"
      expect ")"
      expect "."
      pure body : Parser Clause) state = .ok (encoded, updated)) :
    encoded = body ∧ TableExtension state updated := by
  obtain ⟨ignored, first, firstRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨ignored, second, secondRun, success⟩ := parser_bind_success success
  cases ignored
  obtain ⟨ignored, final, periodRun, success⟩ := parser_bind_success success
  cases ignored
  cases Except.ok.inj success
  exact ⟨rfl, (expect_tableExtension firstRun).trans
    ((expect_tableExtension secondRun).trans (expect_tableExtension periodRun))⟩

theorem cnf_tail_result {fuel state encoded updated}
    (success : StatementTailRun fuel state encoded updated) :
    ∃ named, TableClauseEncoding updated named encoded ∧ TableExtension state updated := by
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
      obtain ⟨rfl, closingExtension⟩ := cnf_closing_result success
      exact ⟨[], .nil, headerExtension.trans ((expect_tableExtension falseRun).trans closingExtension)⟩
    · obtain ⟨body, afterBody, bodyRun, success⟩ := parser_bind_success success
      obtain ⟨named, encoding, bodyExtension⟩ := cnf_literals_result bodyRun
      obtain ⟨rfl, closingExtension⟩ := cnf_closing_result success
      exact ⟨named, encoding.extend closingExtension, headerExtension.trans (bodyExtension.trans closingExtension)⟩

theorem cnf_statement_result {fuel state encoded updated}
    (success : Frontend.statement fuel state = .ok (encoded, updated)) :
    ∃ name named, TableDeclarationEncoding updated (.cnf ⟨name, named⟩) (.cnf encoded) ∧
      SymbolExtension state updated ∧ name ∉ state.clauseNames ∧
      updated.clauseNames = state.clauseNames ++ [name] := by
  obtain ⟨name, afterCnf, opened, namedState, cnfRun, openingRun, nameRun, valid,
    fresh, priorNames, priorVariables, tailRun⟩ := statement_success_decomposition success
  obtain ⟨named, encoding, tailExtension⟩ := cnf_tail_result tailRun
  have headerExtension := (expect_tableExtension cnfRun).trans
    ((expect_tableExtension openingRun).trans (consume_tableExtension nameRun))
  exact ⟨name, named, .cnf updated.variables name encoding,
    headerExtension.toSymbolExtension.trans
      ((symbolExtension_reset namedState [] (namedState.clauseNames ++ [name])).trans
        tailExtension.toSymbolExtension),
    by simpa only [priorNames] using fresh,
    by simpa only [priorNames] using tailRun.clause_names⟩

end Fang.FOFFrontend
