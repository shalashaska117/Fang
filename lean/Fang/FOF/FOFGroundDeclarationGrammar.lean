/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFFormulaGrammar
import Fang.FOF.FOFDeclarationEncoding

namespace Fang.FOFFrontend
open Frontend

theorem raw_ground_statement_grammar {fuel state encoded updated}
    (notCnf : (state.tokens.head?.map Token.text == some "cnf") ≠ true)
    (success : statement fuel state = .ok (encoded, updated)) :
    ∃ name named, TableDeclarationEncoding updated (.fof name named) encoded ∧
      SymbolExtension state updated ∧ name ∉ state.clauseNames ∧
      updated.clauseNames = state.clauseNames ++ [name] ∧
      FOFGrammar.GroundDeclarationTokens (spellings state) name named (spellings updated) := by
  simp only [statement] at success
  obtain ⟨kind, initial, peeked, success⟩ := parser_bind_success success
  rw [peek_run] at peeked
  cases peeked
  by_cases isCnf : (state.tokens.head?.map Token.text == some "cnf") = true
  · exact False.elim (notCnf isCnf)
  · simp only [isCnf] at success
    obtain ⟨kind, initial, peeked, success⟩ := parser_bind_success success
    rw [peek_run] at peeked
    cases peeked
    split at success
    · obtain ⟨ignored, afterFof, fofRun, success⟩ := parser_bind_success success
      cases ignored
      obtain ⟨ignored, opened, opening, success⟩ := parser_bind_success success
      cases ignored
      obtain ⟨offset, positioned, positionRun, success⟩ := parser_bind_success success
      rw [position_run] at positionRun
      cases positionRun
      obtain ⟨name, namedState, consumed, success⟩ := parser_bind_success success
      split at success
      · simp [bind, StateT.bind, failAt_run, Except.bind] at success
      · rename_i validName
        obtain ⟨readState, sameState, readRun, success⟩ := parser_bind_success success
        have same : (namedState, namedState) = (readState, sameState) := Except.ok.inj readRun
        cases same
        split at success
        · simp [bind, StateT.bind, failAt_run, Except.bind] at success
        · rename_i freshGuard
          have fresh : name ∉ namedState.clauseNames := by simpa using freshGuard
          have priorNames := (consume_clause_names consumed).trans
            ((expect_clause_names opening).trans (expect_clause_names fofRun))
          obtain ⟨ignored, reset, resetRun, success⟩ := parser_bind_success success
          cases ignored
          have resetSame : ((), { namedState with clauseNames := namedState.clauseNames ++ [name], variables := [] }) =
              ((), reset) := Except.ok.inj resetRun
          cases resetSame
          obtain ⟨ignored, afterComma, commaRun, success⟩ := parser_bind_success success
          cases ignored
          obtain ⟨role, roleState, roleRun, success⟩ := parser_bind_success success
          rw [peek_run] at roleRun
          cases roleRun
          split at success
          · simp [bind, StateT.bind, fail_run, Except.bind] at success
          · obtain ⟨ignored, afterRole, roleConsumed, success⟩ := parser_bind_success success
            cases ignored
            obtain ⟨ignored, beforeFormula, secondComma, success⟩ := parser_bind_success success
            cases ignored
            obtain ⟨body, afterFormula, formulaRun, success⟩ := parser_bind_success success
            obtain ⟨named, encoding, extension, grammar⟩ := raw_formula_grammar fuel formulaRun
            split at success
            · simp [bind, StateT.bind, fail_run, Except.bind] at success
            · rename_i ground
              have bodyGround : body.Ground := groundFormula_correct body |>.mp (by simpa using ground)
              obtain ⟨next, afterPeek, nextRun, success⟩ := parser_bind_success success
              rw [peek_run] at nextRun
              cases nextRun
              split at success
              · simp [bind, StateT.bind, fail_run, Except.bind] at success
              · obtain ⟨ignored, closed, closing, success⟩ := parser_bind_success success
                cases ignored
                obtain ⟨ignored, final, period, success⟩ := parser_bind_success success
                cases ignored
                have same : (GroundFOF.Declaration.fof body, final) = (encoded, updated) :=
                  Except.ok.inj success
                cases same
                have endExtension := (expect_tableExtension closing).trans (expect_tableExtension period)
                have finalEncoding := encoding.extend endExtension
                refine ⟨name, named, .fof updated.variables name (encoding.ground_iff.mp bodyGround) finalEncoding,
                  ?_, by simpa only [priorNames] using fresh, ?_, ?_⟩
                · exact (expect_tableExtension fofRun).toSymbolExtension.trans
                    ((expect_tableExtension opening).toSymbolExtension.trans
                    ((consume_tableExtension consumed).toSymbolExtension.trans
                    ((symbolExtension_reset namedState [] (namedState.clauseNames ++ [name])).trans
                    ((expect_tableExtension commaRun).toSymbolExtension.trans
                    ((expect_tableExtension roleConsumed).toSymbolExtension.trans
                    ((expect_tableExtension secondComma).toSymbolExtension.trans
                    (extension.trans endExtension).toSymbolExtension))))))
                · have names := (expect_clause_names period).trans ((expect_clause_names closing).trans
                    ((formula_preserves_clause_names formulaRun).trans
                    ((expect_clause_names secondComma).trans ((expect_clause_names roleConsumed).trans
                      (expect_clause_names commaRun)))))
                  simpa only [priorNames] using names
                · have lower : lowerName name = true := by simpa using validName
                  have valid := (lowerName_iff name (lowerName_ascii lower)).mp lower
                  rw [expect_spellings closing, expect_spellings period] at grammar
                  have parsed := FOFGrammar.GroundDeclarationTokens.axiom valid grammar
                    (encoding.ground_iff.mp bodyGround)
                  rw [expect_spellings fofRun, expect_spellings opening, consume_spellings consumed]
                  change FOFGrammar.GroundDeclarationTokens
                    ("fof" :: "(" :: name :: spellings
                      { namedState with clauseNames := namedState.clauseNames ++ [name], variables := [] })
                    name named (spellings updated)
                  rw [expect_spellings commaRun, expect_spellings roleConsumed, expect_spellings secondComma]
                  exact parsed
    · simp [fail_run] at success


end Fang.FOFFrontend
