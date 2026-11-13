/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Soundness of successful executable source decoding with respect to the
independent byte grammar and named first-order semantics.
-/
import Fang.FrontendStatementGrammar
import Fang.FrontendAcceptedTokens
import Fang.FrontendGrammarLexing

namespace Fang.Frontend

open Source.Grammar

def StatementsGrammarResult (before : State) (tokens : List Source.Grammar.Token)
    (encoded : Problem) (after : State) : Prop :=
  ∃ named, ProblemTokens tokens named ∧
    Source.ProblemEncoding (signatureFrom after) (symbolsFrom after) named encoded ∧
    SymbolExtension before after ∧ after.clauseNames = before.clauseNames ++ named.map Source.Clause.name

theorem statements_grammar {fuel state input encoded updated}
    (classified : ClassifiedTokens state.tokens input) (unique : state.clauseNames.Nodup)
    (success : statements fuel state = .ok (encoded, updated)) :
    StatementsGrammarResult state input encoded updated := by
  induction fuel generalizing state input encoded updated with
  | zero => simp [statements, fail_run] at success
  | succ fuel induction =>
      rw [statements_run] at success
      split at success
      · rename_i empty
        cases success
        have noTokens := List.isEmpty_iff.mp empty
        rw [noTokens] at classified
        cases classified
        exact ⟨[], .empty, ⟨by simp, .nil⟩, .refl state, by simp⟩
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
                obtain ⟨namedFirst, middle, firstEncoding, firstExtension, firstGrammar,
                  middleClass, fresh, firstNames⟩ := statement_grammar classified firstRun
                have middleUnique := statement_preserves_unique_clause_names fuel state first afterFirst unique firstRun
                obtain ⟨namedTail, tailGrammar, tailEncoding, tailExtension, tailNames⟩ :=
                  induction middleClass middleUnique tailRun
                have names : final.clauseNames = state.clauseNames ++
                    (namedFirst :: namedTail).map Source.Clause.name := by
                  simp only [tailNames, firstNames, List.map_cons, List.append_assoc, List.singleton_append]
                have finalUnique := statements_preserve_unique_clause_names fuel afterFirst tail final middleUnique tailRun
                have namedUnique : ((namedFirst :: namedTail).map Source.Clause.name).Nodup := by
                  rw [names] at finalUnique
                  exact (List.nodup_append.mp finalUnique).2.1
                exact ⟨namedFirst :: namedTail, .statement firstGrammar tailGrammar,
                  ⟨namedUnique, .cons ⟨variablesFrom afterFirst.variables,
                    (firstEncoding.toSource namedFirst.name).extend_symbols tailExtension⟩ tailEncoding.clauses⟩,
                  firstExtension.trans tailExtension, names⟩

end Fang.Frontend

namespace Fang

open Frontend Source.Grammar

theorem decode_sound {input : String} {encoded : Problem}
    (success : decodeProblem input = .ok encoded) :
    ∃ named final, Source.Grammar.Parses (spelling input) named ∧
      Source.ProblemEncoding (signatureFrom final) (symbolsFrom final) named encoded := by
  obtain ⟨decoded, decodedSuccess, rfl⟩ := decodeProblem_success success
  obtain ⟨raw, final, tokenized, parsed, _, _, _, _⟩ := decodeProblemWithSignature_success decodedSuccess
  obtain ⟨tokens, classified⟩ := statements_classifies_input parsed
  obtain ⟨named, grammar, encoding, _, _⟩ := statements_grammar classified (by simp) parsed
  exact ⟨named, final,
    (grammar_parses_iff_tokenized input named).mpr ⟨raw, tokens, tokenized, classified, grammar⟩,
    encoding⟩

theorem decode_satisfiable_iff {input : String} {encoded : Problem}
    (success : decodeProblem input = .ok encoded) :
    Source.Grammar.BytesSatisfiable (spelling input) ↔ Fang.Satisfiable encoded := by
  obtain ⟨named, final, parsed, encoding⟩ := decode_sound success
  constructor
  · rintro ⟨other, otherParsed, model⟩
    have same := parsed.unique otherParsed
    subst other
    exact encoding.satisfiable_iff.mp model
  · intro model
    exact ⟨named, parsed, encoding.satisfiable_iff.mpr model⟩

theorem decoded_refutation_unsat {input : String} {encoded : Problem}
    (success : decodeProblem input = .ok encoded) (certificate : Certificate)
    (accepted : check (preprocess encoded) certificate = true) :
    ¬ Source.Grammar.BytesSatisfiable (spelling input) := by
  obtain ⟨named, final, parsed, encoding⟩ := decode_sound success
  exact original_bytes_unsat_of_witness parsed encoding certificate accepted

#print axioms Frontend.statements_grammar
#print axioms decode_sound
#print axioms decode_satisfiable_iff
#print axioms decoded_refutation_unsat

end Fang
