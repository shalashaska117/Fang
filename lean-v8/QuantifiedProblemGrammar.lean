/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Unchecked problem-decoder composition. Numeric refutation remains a premise. -/
import QuantifiedDeclarationGrammar
import QuantifiedByteGrammar
import FOFCNFGrammar

namespace Fang.QuantifiedFrontend
open Frontend FOFFrontend NamedQuantified.Grammar

theorem statement_cnf_run (fuel : Nat) (state : State)
    (isCnf : (state.tokens.head?.map Token.text == some "cnf") = true) :
    statement fuel state = (do
      let (clause, updated) ← Frontend.statement fuel state
      pure (NamedQuantified.NumericDeclaration.cnf clause, updated)) := by
  simp only [statement, bind, StateT.bind, peek_run, Except.bind, isCnf,
    ↓reduceIte, pure, StateT.pure, Except.pure]

theorem raw_statement_grammar {fuel state encoded updated}
    (success : statement fuel state = .ok (encoded, updated)) :
    ∃ named, TableDeclarationEncoding updated named encoded ∧ SymbolExtension state updated ∧
      named.name ∉ state.clauseNames ∧ updated.clauseNames = state.clauseNames ++ [named.name] ∧
      DeclarationTokens (spellings state) named (spellings updated) := by
  by_cases isCnf : (state.tokens.head?.map Token.text == some "cnf") = true
  · rw [statement_cnf_run fuel state isCnf] at success
    cases parsed : Frontend.statement fuel state with
    | error error => simp [parsed, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨clause, final⟩
      simp only [parsed, bind, Except.bind, pure, Except.pure] at success
      cases success
      obtain ⟨named, encoding, extension, grammar, fresh, history⟩ :=
        FOFFrontend.raw_cnf_statement_grammar parsed
      have converted : TableDeclarationEncoding updated (.cnf named) (.cnf clause) := by
        cases encoding with
        | cnf variables name relation => exact .cnf variables name relation
      exact ⟨.cnf named, converted, extension, fresh, history, .cnf grammar⟩
  · obtain ⟨name, named, encoding, extension, fresh, history, grammar⟩ :=
      raw_quantified_statement_grammar isCnf success
    exact ⟨.fof name named, encoding, extension, fresh, history, grammar⟩

theorem raw_statements_grammar (fuel : Nat) :
    ∀ {state encoded updated}, state.clauseNames.Nodup →
      statements fuel state = .ok (encoded, updated) →
      ∃ named, Source.RelatedLists (TableDeclarationEncoding updated) named encoded ∧
        SymbolExtension state updated ∧
        updated.clauseNames = state.clauseNames ++ named.map NamedQuantified.Declaration.name ∧
        (state.clauseNames ++ named.map NamedQuantified.Declaration.name).Nodup ∧
        DeclarationsTokens (spellings state) named := by
  induction fuel with
  | zero =>
    intro state encoded updated unique success
    simp [statements, fail_run] at success
  | succ fuel ih =>
    intro state encoded updated unique success
    simp only [statements] at success
    obtain ⟨next, initial, peeked, success⟩ := parser_bind_success success
    rw [peek_run] at peeked
    cases peeked
    split at success
    · rename_i empty
      cases Except.ok.inj success
      refine ⟨[], .nil, .refl state, by simp, by simpa using unique, ?_⟩
      cases tokens : state.tokens with
      | nil => simpa [spellings, tokens] using DeclarationsTokens.nil
      | cons token rest => simp [tokens] at empty
    · obtain ⟨first, afterFirst, firstRun, success⟩ := parser_bind_success success
      obtain ⟨namedFirst, firstEncoding, firstExtension, fresh, firstHistory, firstGrammar⟩ :=
        raw_statement_grammar firstRun
      have firstUnique : afterFirst.clauseNames.Nodup := by
        rw [firstHistory]
        apply List.nodup_append.mpr
        refine ⟨unique, by simp, ?_⟩
        intro left member right singleton
        have same : right = namedFirst.name := by simpa using singleton
        subst right
        intro same
        exact fresh (same ▸ member)
      obtain ⟨tail, final, tailRun, success⟩ := parser_bind_success success
      cases Except.ok.inj success
      obtain ⟨namedTail, tailEncoding, tailExtension, tailHistory, tailUnique, tailGrammar⟩ :=
        ih firstUnique tailRun
      refine ⟨namedFirst :: namedTail, .cons (firstEncoding.extend tailExtension) tailEncoding,
        firstExtension.trans tailExtension, ?_, ?_, .cons firstGrammar tailGrammar⟩
      · simpa only [firstHistory, List.map_cons, List.append_assoc, List.singleton_append] using tailHistory
      · simpa only [firstHistory, List.map_cons, List.append_assoc, List.singleton_append] using tailUnique

theorem decode_byte_grammar {input decoded} (success : decode input = .ok decoded) :
    ∃ named, Parses (Source.Grammar.spelling input) named ∧
      NamedQuantified.ProblemEncoding (signatureFrom decoded.state) (symbolsFrom decoded.state)
        named decoded.declarations := by
  cases tokenized : tokenize input with
  | error error => simp [decode, tokenized, bind, Except.bind] at success
  | ok tokens =>
    cases parsed : statements (tokens.length + 1) { tokens, endOffset := input.utf8ByteSize } with
    | error error => simp [decode, tokenized, parsed, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨declarations, state⟩
      simp only [decode, tokenized, parsed, bind, Except.bind, pure, Except.pure] at success
      cases success
      obtain ⟨named, encoding, _, _, unique, grammar⟩ :=
        raw_statements_grammar (tokens.length + 1) (by simp) parsed
      have names : (named.map NamedQuantified.Declaration.name).Nodup := by simpa using unique
      exact ⟨named, ⟨tokens, (quantified_tokenize_bytes_iff input tokens).mp tokenized, grammar, names⟩,
        tableDeclarations_toSource encoding names⟩

theorem decode_bytes_satisfiable_iff {input decoded} (success : decode input = .ok decoded) :
    BytesSatisfiable (Source.Grammar.spelling input) ↔
      NamedQuantified.NumericSatisfiable decoded.declarations := by
  obtain ⟨named, parsed, encoding⟩ := decode_byte_grammar success
  constructor
  · rintro ⟨other, otherParsed, satisfiable⟩
    obtain rfl := parsed.unique otherParsed
    exact encoding.satisfiable_iff.mp satisfiable
  · intro satisfiable
    exact ⟨named, parsed, encoding.satisfiable_iff.mpr satisfiable⟩

/-- Conditional transport: preprocessing and a numeric certificate checker
    must still establish the refutation premise for these declarations. -/
theorem decode_bytes_unsat {input decoded} (success : decode input = .ok decoded)
    (refuted : ¬ NamedQuantified.NumericSatisfiable decoded.declarations) :
    ¬ BytesSatisfiable (Source.Grammar.spelling input) := by
  obtain ⟨named, parsed, encoding⟩ := decode_byte_grammar success
  rintro ⟨other, otherParsed, satisfiable⟩
  obtain rfl := parsed.unique otherParsed
  exact encoding.unsat refuted satisfiable

end Fang.QuantifiedFrontend
