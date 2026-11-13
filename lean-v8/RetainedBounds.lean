/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Retained CNF occurrences use the final original function table. -/
import MixedLayout
import QuantifiedProblemGrammar
import SkolemModel

namespace Fang.QuantifiedCertificate
open Frontend QuantifiedFOF.Skolem

theorem symbolIndex_below {symbols : List Symbol} {name : String} {id : Nat}
    (found : symbolIndex name symbols 0 = some id) : id < symbols.length := by
  have first : FirstNameAt (symbols.map Symbol.name) name id := by
    apply (namedIndex_first_iff name (symbols.map Symbol.name) id).mp
    simpa only [symbolIndex_eq_namedIndex] using found
  simpa only [List.length_map] using first.1

mutual
theorem tableTerm_below {state named encoded} (encoding : TableTermEncoding state named encoded) :
    TermBelow state.functions.length encoded := by
  cases encoding with
  | var => simp only [TermBelow]
  | app name id arguments terms found checked children =>
    simp only [TermBelow]
    exact ⟨symbolIndex_below found, tableTerms_below children⟩

theorem tableTerms_below {state named encoded} (encoding : TableTermsEncoding state named encoded) :
    ∀ term ∈ encoded, TermBelow state.functions.length term := by
  cases encoding with
  | nil => simp
  | cons head tail =>
    intro term member
    rcases List.mem_cons.mp member with rfl | member
    · exact tableTerm_below head
    · exact tableTerms_below tail term member
end

theorem tableLiteral_below {state named encoded} (encoding : TableLiteralEncoding state named encoded) :
    ∀ term ∈ encoded.atom.args, TermBelow state.functions.length term :=
  tableTerms_below encoding.arguments

theorem tableClause_below {state named encoded} (encoding : TableClauseEncoding state named encoded) :
    ∀ literal ∈ encoded, ∀ term ∈ literal.atom.args, TermBelow state.functions.length term := by
  induction encoding with
  | nil => simp
  | cons head tail ih =>
    intro literal member
    rcases List.mem_cons.mp member with rfl | member
    · exact tableLiteral_below head
    · exact ih literal member

theorem tableDeclarations_retained_below {state named encoded}
    (encoding : Source.RelatedLists (QuantifiedFrontend.TableDeclarationEncoding state) named encoded) :
    ∀ clause ∈ retained encoded, ∀ literal ∈ clause, ∀ term ∈ literal.atom.args,
      TermBelow state.functions.length term := by
  induction encoding with
  | nil => simp [retained]
  | cons head tail ih =>
    cases head with
    | cnf variables name relation =>
      intro clause member
      rcases List.mem_cons.mp member with rfl | member
      · exact tableClause_below (state := {state with variables}) relation
      · exact ih clause member
    | fof variables name closed relation => exact ih

/-- The accepted statement proof transports each earlier clause encoding to
    the complete final symbol table, including symbols encountered later. -/
theorem decode_table_encoding {input decoded}
    (success : QuantifiedFrontend.decode input = .ok decoded) :
    ∃ named, Source.RelatedLists (QuantifiedFrontend.TableDeclarationEncoding decoded.state)
      named decoded.declarations := by
  cases tokenized : QuantifiedFrontend.tokenize input with
  | error error => simp [QuantifiedFrontend.decode, tokenized, bind, Except.bind] at success
  | ok tokens =>
    cases parsed : QuantifiedFrontend.statements (tokens.length + 1)
        { tokens, endOffset := input.utf8ByteSize } with
    | error error => simp [QuantifiedFrontend.decode, tokenized, parsed, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨declarations, state⟩
      simp only [QuantifiedFrontend.decode, tokenized, parsed, bind, Except.bind, pure, Except.pure] at success
      cases success
      obtain ⟨named, encoding, _⟩ :=
        QuantifiedFrontend.raw_statements_grammar (tokens.length + 1) (by simp) parsed
      exact ⟨named, encoding⟩

/-- This conclusion unfolds to the pipeline's ProblemBelow predicate. It does
    not require each function to occur in a retained clause or in an earlier declaration. -/
theorem decode_retained_functions_below {input decoded}
    (success : QuantifiedFrontend.decode input = .ok decoded) :
    ∀ clause ∈ retained decoded.declarations, ∀ literal ∈ clause, ∀ term ∈ literal.atom.args,
      TermBelow decoded.state.functions.length term := by
  obtain ⟨named, encoding⟩ := decode_table_encoding success
  exact tableDeclarations_retained_below encoding

end Fang.QuantifiedCertificate
