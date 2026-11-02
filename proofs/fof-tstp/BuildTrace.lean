/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.Ancestry
import Fang.FOF.TSTP.DisjointDerivation
import Fang.FOF.TSTP.LeafNames

namespace Fang.FofTstpExport

/-- The exact record passed to the unchanged CNF trace builder. This is only a
    projection of retained FOF preprocessing data, not a second builder. -/
def traceProblem (decoded : FOFFrontend.Decoded) (items : List Leaf) : TstpExport.NamedProblem := {
  signature := FOFVersioned.signature decoded
  functions := decoded.state.functions
  predicates := decoded.state.predicates
  names := items.map Leaf.rawName
}

theorem build_trace {decoded : FOFFrontend.Decoded} {certificate : Certificate} {output : Export}
    (built : build decoded certificate = .ok output) :
    TstpExport.build (traceProblem decoded output.leaves) certificate = .ok output.trace := by
  unfold build at built
  cases leafEq : leaves decoded with
  | error reason => simp [leafEq, bind, Except.bind] at built
  | ok items =>
    simp only [leafEq, bind, Except.bind] at built
    split at built
    · contradiction
    · split at built
      · contradiction
      · rename_i trace traceEq
        cases built
        exact traceEq

theorem build_trace_endpoint {decoded : FOFFrontend.Decoded} {certificate : Certificate} {output : Export}
    (built : build decoded certificate = .ok output) :
    output.trace.signature = traceProblem decoded output.leaves ∧
      output.trace.rows.getLast?.map TstpExport.Row.name = some output.trace.finalName ∧
      output.trace.rows.getLast?.map TstpExport.Row.clause = some [] :=
  TstpExport.build_endpoint (build_trace built)

/-- Name uniqueness and source/generated disjointness are explicit premises
    here. Their FOF leaf instantiation is a separate required proof. -/
theorem build_typed_derivation {decoded : FOFFrontend.Decoded} {certificate : Certificate} {output : Export}
    (built : build decoded certificate = .ok output)
    (disjoint : TstpExport.BuilderProof.DisjointNames (output.leaves.map Leaf.rawName))
    (unique : (output.leaves.map Leaf.rawName).Nodup) :
    TstpExport.Derivation output.trace.signature output.trace.rows := by
  have derived := TstpExport.BuilderProof.build_derivation_disjoint
    (traceProblem decoded output.leaves) certificate output.trace disjoint unique (build_trace built)
  simpa only [(build_trace_endpoint built).1] using derived

theorem decoded_source_names_unique {input : String} {decoded : FOFFrontend.Decoded}
    (success : FOFFrontend.decode input = .ok decoded) : decoded.state.clauseNames.Nodup := by
  cases tokenized : FOFFrontend.tokenize input with
  | error reason => simp [FOFFrontend.decode, tokenized, bind, Except.bind] at success
  | ok tokens =>
    cases parsed : FOFFrontend.statements (tokens.length + 1)
        { tokens, endOffset := input.utf8ByteSize } with
    | error reason => simp [FOFFrontend.decode, tokenized, parsed, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨declarations, state⟩
      simp only [FOFFrontend.decode, tokenized, parsed, bind, Except.bind, pure, Except.pure] at success
      cases success
      obtain ⟨named, _, _, history, unique, _⟩ :=
        FOFFrontend.raw_statements_grammar (tokens.length + 1) (by simp) parsed
      rw [history]
      exact unique

/-- Actual successful FOF decoding and building discharge both name premises.
    This establishes the unchanged typed clause trace; the renderer's inserted
    source-formula rows still require their own sequence correspondence. -/
theorem decoded_build_typed_derivation {input : String} {decoded : FOFFrontend.Decoded}
    {certificate : Certificate} {output : Export}
    (decodedOk : FOFFrontend.decode input = .ok decoded)
    (built : build decoded certificate = .ok output) :
    TstpExport.Derivation output.trace.signature output.trace.rows := by
  apply build_typed_derivation built
  · exact collectLeaves_generated_disjoint (build_source built).2
  · exact collectLeaves_names_nodup (decoded_source_names_unique decodedOk) (build_source built).2

end Fang.FofTstpExport
