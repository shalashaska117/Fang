/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import FOFEncodingRun
import FOFNameState
import Fang.FrontendDisjunctionGrammar

namespace Fang.FOFFrontend
open Frontend

/- Variable tables belong to declarations. Later declarations may reset them;
   function and predicate tables are shared and may only extend known entries. -/
inductive TableDeclarationEncoding (state : State) :
    NamedFOF.Declaration → GroundFOF.Declaration → Prop where
  | cnf (variables : List String) (name : String) {named encoded}
      (relation : TableClauseEncoding { state with variables } named encoded) :
      TableDeclarationEncoding state (.cnf ⟨name, named⟩) (.cnf encoded)
  | fof (variables : List String) (name : String) {named encoded}
      (ground : named.Ground)
      (relation : TableFormulaEncoding { state with variables } named encoded) :
      TableDeclarationEncoding state (.fof name named) (.fof encoded)

theorem TableDeclarationEncoding.toSource {state named encoded}
    (encoding : TableDeclarationEncoding state named encoded) :
    NamedFOF.DeclarationEncoding (signatureFrom state) (symbolsFrom state) named encoded := by
  cases encoding with
  | cnf variables name relation => exact .cnf (variablesFrom variables) (relation.toSource name)
  | fof variables name ground relation => exact .fof name (variablesFrom variables) ground relation.toSource

theorem TableDeclarationEncoding.extend {before after named encoded}
    (encoding : TableDeclarationEncoding before named encoded) (extension : SymbolExtension before after) :
    TableDeclarationEncoding after named encoded := by
  cases encoding with
  | cnf variables name relation =>
      exact .cnf variables name (relation.extend (extension.withVariables variables))
  | fof variables name ground relation =>
      exact .fof variables name ground (relation.extend (extension.withVariables variables))

theorem tableDeclarations_extend {before after named encoded}
    (encoding : Source.RelatedLists (TableDeclarationEncoding before) named encoded)
    (extension : SymbolExtension before after) :
    Source.RelatedLists (TableDeclarationEncoding after) named encoded := by
  induction encoding with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.extend extension) ih

theorem tableDeclarations_toSource {state named encoded}
    (encoding : Source.RelatedLists (TableDeclarationEncoding state) named encoded)
    (names : (named.map NamedFOF.Declaration.name).Nodup) :
    NamedFOF.ProblemEncoding (signatureFrom state) (symbolsFrom state) named encoded := by
  refine ⟨names, ?_⟩
  clear names
  induction encoding with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.toSource ih

theorem tableDeclarations_unsat_of_check {state named encoded}
    (encoding : Source.RelatedLists (TableDeclarationEncoding state) named encoded)
    (names : (named.map NamedFOF.Declaration.name).Nodup) (certificate : Fang.Certificate)
    (accepted : Fang.check (GroundFOF.prepareDeclarations encoded) certificate = true) :
    ¬ NamedFOF.Satisfiable named :=
  (tableDeclarations_toSource encoding names).unsat_of_check certificate accepted

theorem non_cnf_statement_result {fuel state encoded updated}
    (notCnf : (state.tokens.head?.map Token.text == some "cnf") ≠ true)
    (success : statement fuel state = .ok (encoded, updated)) :
    ∃ name named, TableDeclarationEncoding updated (.fof name named) encoded ∧
      SymbolExtension state updated ∧ name ∉ state.clauseNames ∧
      updated.clauseNames = state.clauseNames ++ [name] := by
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
      · obtain ⟨readState, sameState, readRun, success⟩ := parser_bind_success success
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
            obtain ⟨named, encoding, extension⟩ := formula_result fuel formulaRun
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
                  ?_, by simpa only [priorNames] using fresh, ?_⟩
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
    · simp [fail_run] at success

theorem statement_cnf_run (fuel : Nat) (state : State)
    (isCnf : (state.tokens.head?.map Token.text == some "cnf") = true) :
    statement fuel state = (do
      let (clause, updated) ← Frontend.statement fuel state
      pure (GroundFOF.Declaration.cnf clause, updated)) := by
  simp only [statement, bind, StateT.bind, peek_run, Except.bind, isCnf,
    ↓reduceIte, pure, StateT.pure, Except.pure]

theorem fof_statement_result_full {fuel state encoded updated}
    (success : statement fuel state = .ok (.fof encoded, updated)) :
    ∃ name named, TableDeclarationEncoding updated (.fof name named) (.fof encoded) ∧
      SymbolExtension state updated ∧ name ∉ state.clauseNames ∧
      updated.clauseNames = state.clauseNames ++ [name] := by
  by_cases isCnf : (state.tokens.head?.map Token.text == some "cnf") = true
  · rw [statement_cnf_run fuel state isCnf] at success
    cases parsed : Frontend.statement fuel state with
    | error error => simp [parsed, bind, Except.bind] at success
    | ok pair =>
        rcases pair with ⟨clause, final⟩
        simp only [parsed, bind, Except.bind, pure, Except.pure] at success
        cases success
  · exact non_cnf_statement_result isCnf success

theorem fof_statement_result {fuel state encoded updated}
    (success : statement fuel state = .ok (.fof encoded, updated)) :
    ∃ name named, TableDeclarationEncoding updated (.fof name named) (.fof encoded) ∧
      SymbolExtension state updated := by
  obtain ⟨name, named, encoding, extension, _, _⟩ := fof_statement_result_full success
  exact ⟨name, named, encoding, extension⟩

end Fang.FOFFrontend
