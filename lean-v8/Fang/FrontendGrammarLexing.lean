/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Exact correspondence between grammar tokenization and successfully classified
output of the actual tokenizer. A successful raw tokenization alone does not
classify its words and need not satisfy the grammar.
-/
import Fang.FrontendClassification
import Fang.SourceAsciiValidity

namespace Fang.Frontend

open Source.Grammar

theorem grammar_tokenization_iff_classified (input : String)
    (tokens : List Source.Grammar.Token) :
    Source.Grammar.Tokenization (spelling input) tokens ↔
      ∃ raw, tokenize input = .ok raw ∧ ClassifiedTokens raw tokens := by
  constructor
  · intro tokenized
    exact grammar_tokenization_complete input tokens tokenized.string_ascii tokenized
  · rintro ⟨raw, success, classified⟩
    exact tokenize_toGrammar input raw success tokens classified

theorem grammar_parses_iff_tokenized (input : String) (problem : Source.Problem) :
    Source.Grammar.Parses (spelling input) problem ↔
      ∃ raw tokens, tokenize input = .ok raw ∧ ClassifiedTokens raw tokens ∧
        Source.Grammar.ProblemTokens tokens problem := by
  constructor
  · rintro ⟨tokens, tokenized, parsed⟩
    obtain ⟨raw, success, classified⟩ :=
      (grammar_tokenization_iff_classified input tokens).mp tokenized
    exact ⟨raw, tokens, success, classified, parsed⟩
  · rintro ⟨raw, tokens, success, classified, parsed⟩
    exact ⟨tokens, (grammar_tokenization_iff_classified input tokens).mpr
      ⟨raw, success, classified⟩, parsed⟩

theorem grammar_parses_tokenize_success {input : String} {problem : Source.Problem}
    (parsed : Source.Grammar.Parses (spelling input) problem) :
    ∃ raw, tokenize input = .ok raw := by
  obtain ⟨raw, _, success, _⟩ := (grammar_parses_iff_tokenized input problem).mp parsed
  exact ⟨raw, success⟩

#print axioms grammar_tokenization_iff_classified
#print axioms grammar_parses_iff_tokenized
#print axioms grammar_parses_tokenize_success

end Fang.Frontend
