/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Every decoded source clause passes the actual exported-signature validator.
This proves checks for represented occurrences, not for unused table entries.
-/
import Fang.FrontendSoundness
import Fang.FrontendSignatureExport

namespace Fang.Frontend

theorem TableClauseEncoding.export_after_symbols {before after named encoded}
    (encoding : TableClauseEncoding before named encoded)
    (extension : SymbolExtension before after) (problem : Problem) :
    clauseWellFormed (exportedProblem after problem) encoded = true := by
  have preserved : TableClauseEncoding { after with variables := before.variables } named encoded :=
    encoding.extend (extension.withVariables before.variables)
  exact tableClause_export_wellFormed preserved problem

theorem statements_export_valid {fuel state input encoded updated}
    (classified : ClassifiedTokens state.tokens input) (unique : state.clauseNames.Nodup)
    (success : statements fuel state = .ok (encoded, updated)) :
    encoded.all (clauseWellFormed (exportedProblem updated encoded)) = true := by
  induction fuel generalizing state input encoded updated with
  | zero => simp [statements, fail_run] at success
  | succ fuel induction =>
      rw [statements_run] at success
      split at success
      · cases success
        rfl
      · cases firstRun : statement fuel state with
        | error error => simp [firstRun, bind, Except.bind] at success
        | ok pair =>
            rcases pair with ⟨first, afterFirst⟩
            cases tailRun : statements fuel afterFirst with
            | error error => simp [firstRun, tailRun, bind, Except.bind] at success
            | ok pair =>
                rcases pair with ⟨tail, final⟩
                simp [firstRun, tailRun, bind, Except.bind, pure, Except.pure] at success
                rcases success with ⟨rfl, rfl⟩
                obtain ⟨namedFirst, middle, firstEncoding, _, _, middleClass, _, _⟩ :=
                  statement_grammar classified firstRun
                have middleUnique := statement_preserves_unique_clause_names fuel state first
                  afterFirst unique firstRun
                obtain ⟨_, _, _, tailExtension, _⟩ :=
                  statements_grammar middleClass middleUnique tailRun
                have firstValid := firstEncoding.export_after_symbols tailExtension (first :: tail)
                have tailValid := induction middleClass middleUnique tailRun
                simp only [List.all_cons, firstValid, Bool.true_and]
                exact tailValid

end Fang.Frontend

namespace Fang

open Frontend

theorem decoded_source_validates {input : String} {decoded : DecodedProblem}
    (success : decodeProblemWithSignature input = .ok decoded) :
    decoded.problem.all (clauseWellFormed decoded) = true := by
  obtain ⟨raw, final, _, parsed, exported⟩ := decodeProblemWithSignature_exported success
  obtain ⟨tokens, classified⟩ := statements_classifies_input parsed
  have valid := statements_export_valid classified (by simp) parsed
  simpa only [← exported] using valid

#print axioms Frontend.TableClauseEncoding.export_after_symbols
#print axioms Frontend.statements_export_valid
#print axioms decoded_source_validates

end Fang
