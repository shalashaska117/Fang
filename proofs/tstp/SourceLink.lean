/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Acceptance

namespace Fang.TstpExport

open Frontend Source.Grammar

theorem decodeNamed_success {input : String} {decoded : NamedProblem}
    (success : decodeNamed input = .ok decoded) :
    ∃ tokens state,
      Frontend.tokenize input = .ok tokens ∧
      Frontend.statements (tokens.length + 1) { tokens, endOffset := input.utf8ByteSize } =
        .ok (decoded.signature.problem, state) ∧
      decoded.functions = state.functions ∧ decoded.predicates = state.predicates ∧
      decoded.names = state.clauseNames := by
  cases tokenized : Frontend.tokenize input with
  | error error => simp [decodeNamed, tokenized, bind, Except.bind] at success
  | ok tokens =>
    cases parsed : Frontend.statements (tokens.length + 1)
        { tokens, endOffset := input.utf8ByteSize } with
    | error error => simp [decodeNamed, tokenized, parsed, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨problem, state⟩
      simp [decodeNamed, tokenized, parsed, bind, Except.bind, pure, Except.pure] at success
      subst decoded
      exact ⟨tokens, state, rfl, parsed, rfl, rfl, rfl⟩

/-- Names and symbol tables retained by the actual export decoder are the ones
    used by the established original-byte grammar and semantic encoding. -/
theorem decodeNamed_source {input : String} {decoded : NamedProblem}
    (success : decodeNamed input = .ok decoded) :
    ∃ named state,
      Source.Grammar.Parses (spelling input) named ∧
      Source.ProblemEncoding (signatureFrom state) (symbolsFrom state)
        named decoded.signature.problem ∧
      decoded.functions = state.functions ∧ decoded.predicates = state.predicates ∧
      decoded.names = named.map Source.Clause.name := by
  obtain ⟨raw, state, tokenized, parsed, functions, predicates, names⟩ :=
    decodeNamed_success success
  obtain ⟨tokens, classified⟩ := Frontend.statements_classifies_input parsed
  obtain ⟨named, grammar, encoding, _, history⟩ :=
    Frontend.statements_grammar classified (by simp) parsed
  refine ⟨named, state,
    (grammar_parses_iff_tokenized input named).mpr ⟨raw, tokens, tokenized, classified, grammar⟩,
    encoding, functions, predicates, ?_⟩
  simpa using names.trans history

end Fang.TstpExport
