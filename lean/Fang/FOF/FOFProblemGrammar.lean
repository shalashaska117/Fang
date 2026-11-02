/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFGroundDeclarationGrammar
import Fang.FOF.FOFCNFGrammar
import Fang.FOF.FOFLexing

namespace Fang.FOFGrammar

inductive DeclarationTokens : List String → NamedFOF.Declaration → List String → Prop where
  | cnf {input clause rest} (parsed : CNFDeclarationTokens input clause rest) :
      DeclarationTokens input (.cnf clause) rest
  | fof {input name formula rest} (parsed : GroundDeclarationTokens input name formula rest) :
      DeclarationTokens input (.fof name formula) rest

inductive DeclarationsTokens : List String → List NamedFOF.Declaration → Prop where
  | nil : DeclarationsTokens [] []
  | cons {input middle first rest} (head : DeclarationTokens input first middle)
      (tail : DeclarationsTokens middle rest) : DeclarationsTokens input (first :: rest)

def Parses (bytes : List UInt8) (named : List NamedFOF.Declaration) : Prop :=
  ∃ raw, FOFFrontend.FofByteTokenization bytes 0 raw ∧
    DeclarationsTokens (raw.map Frontend.Token.text) named ∧
    (named.map NamedFOF.Declaration.name).Nodup

def BytesSatisfiable (bytes : List UInt8) : Prop :=
  ∃ named, Parses bytes named ∧ NamedFOF.Satisfiable named

end Fang.FOFGrammar

namespace Fang.FOFFrontend
open Frontend FOFGrammar

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
      obtain ⟨named, encoding, extension, grammar, fresh, history⟩ := raw_cnf_statement_grammar parsed
      exact ⟨.cnf named, encoding, extension, fresh, history, .cnf grammar⟩
  · obtain ⟨name, named, encoding, extension, fresh, history, grammar⟩ :=
      raw_ground_statement_grammar isCnf success
    exact ⟨.fof name named, encoding, extension, fresh, history, .fof grammar⟩

theorem raw_statements_grammar (fuel : Nat) :
    ∀ {state encoded updated}, state.clauseNames.Nodup →
      statements fuel state = .ok (encoded, updated) →
      ∃ named, Source.RelatedLists (TableDeclarationEncoding updated) named encoded ∧
        SymbolExtension state updated ∧
        updated.clauseNames = state.clauseNames ++ named.map NamedFOF.Declaration.name ∧
        (state.clauseNames ++ named.map NamedFOF.Declaration.name).Nodup ∧
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
      NamedFOF.ProblemEncoding (signatureFrom decoded.state) (symbolsFrom decoded.state)
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
      have names : (named.map NamedFOF.Declaration.name).Nodup := by simpa using unique
      exact ⟨named, ⟨tokens, (fof_tokenize_bytes_iff input tokens).mp tokenized, grammar, names⟩,
        tableDeclarations_toSource encoding names⟩

end Fang.FOFFrontend
