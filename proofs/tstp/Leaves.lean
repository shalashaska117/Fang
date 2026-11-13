/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Pruning

namespace Fang.TstpExport.BuilderProof

theorem related_at_right {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (related : Source.RelatedLists relation inputs outputs) (index : Nat) (output : β)
    (found : outputs[index]? = some output) :
    ∃ input, inputs[index]? = some input ∧ relation input output := by
  induction related generalizing index with
  | nil => simp at found
  | @cons head first tail rest headRelated tailRelated ih =>
    cases index with
    | zero =>
      have same : first = output := by simpa using found
      exact ⟨head, by simp, by simpa only [same] using headRelated⟩
    | succ index =>
      obtain ⟨input, inputAt, relation⟩ := ih index (by simpa using found)
      exact ⟨input, by simpa using inputAt, relation⟩

/-- Indexed source identity and the original clause-local variable encoding.
    The source grammar and encoding come from the actual unchanged decoder. -/
theorem decoded_input_leaf (input : String) (problem : NamedProblem)
    (source : Nat) (name : String) (raw : Clause)
    (decoded : decodeNamed input = .ok problem)
    (nameAt : problem.names[source]? = some name)
    (rawAt : problem.signature.problem[source]? = some raw) :
    ∃ original state clause variables,
      Source.Grammar.Parses (Source.Grammar.spelling input) original ∧
      original[source]? = some clause ∧ clause.name = name ∧
      problem.functions = state.functions ∧ problem.predicates = state.predicates ∧
      Source.ClauseEncoding (Frontend.signatureFrom state) (Frontend.symbolsFrom state)
        variables clause raw := by
  obtain ⟨original, state, parsed, encoding, functions, predicates, names⟩ := decodeNamed_source decoded
  obtain ⟨clause, clauseAt, variables, clauseEncoding⟩ :=
    related_at_right encoding.clauses source raw rawAt
  have label : some clause.name = some name := by
    simpa only [names, List.getElem?_map, clauseAt, Option.map_some] using nameAt
  exact ⟨original, state, clause, variables, parsed, clauseAt, Option.some.inj label,
    functions, predicates, clauseEncoding⟩

theorem build_input_leaf (input : String) (problem : NamedProblem) (certificate : Certificate)
    (output : Export) (row : Row) (source : Nat) (name : String)
    (decoded : decodeNamed input = .ok problem) (built : build problem certificate = .ok output)
    (member : row ∈ output.rows) (tag : row.origin = .input source name) :
    row.name = name ∧ ∃ original state clause variables,
      Source.Grammar.Parses (Source.Grammar.spelling input) original ∧
      original[source]? = some clause ∧ clause.name = name ∧
      problem.functions = state.functions ∧ problem.predicates = state.predicates ∧
      Source.ClauseEncoding (Frontend.signatureFrom state) (Frontend.symbolsFrom state)
        variables clause row.clause := by
  obtain ⟨clauses, _, origins⟩ := build_origins problem certificate output built
  have origin := origins row member
  simp only [CertificateRow, tag] at origin
  obtain ⟨_, _, _, nameAt, sameName, rawAt⟩ := origin
  exact ⟨sameName, decoded_input_leaf input problem source name row.clause decoded nameAt rawAt⟩

end Fang.TstpExport.BuilderProof
