/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFGroundComplete
import Fang.FOF.FOFCNFComplete
import Fang.FOF.FOFDecodeFuel
import Fang.FOF.FOFByteSemantics

namespace Fang.FOFFrontend
open Frontend FOFGrammar

theorem raw_statement_complete {input named rest} (parsed : DeclarationTokens input named rest)
    (signature : Source.Signature) (state : State) (words : spellings state = input)
    (wellFormed : named.WellFormed signature) (compatible : SignatureCompatible signature state)
    (fresh : named.name ∉ state.clauseNames) :
    RawDeclarationCompletion signature state named rest := by
  cases parsed with
  | cnf grammar => exact raw_cnf_declaration_complete grammar signature state words wellFormed compatible fresh
  | fof grammar => exact raw_ground_statement_complete grammar signature state words wellFormed.2 compatible fresh

def RawStatementsCompletion (signature : Source.Signature) (state : State)
    (named : List NamedFOF.Declaration) : Prop :=
  ∃ fuel encoded updated, statements fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧
    updated.clauseNames = state.clauseNames ++ named.map NamedFOF.Declaration.name ∧
    SymbolExtension state updated

theorem raw_statements_complete {input named} (parsed : DeclarationsTokens input named)
    (signature : Source.Signature) (state : State) (words : spellings state = input)
    (wellFormed : NamedFOF.ProblemWellFormed signature named)
    (unique : (named.map NamedFOF.Declaration.name).Nodup)
    (compatible : SignatureCompatible signature state)
    (fresh : ∀ declaration ∈ named, declaration.name ∉ state.clauseNames) :
    RawStatementsCompletion signature state named := by
  induction parsed generalizing state with
  | nil =>
    have empty : state.tokens = [] := List.map_eq_nil_iff.mp words
    refine ⟨1, [], state, ?_, compatible, by simp, .refl state⟩
    simp [statements, bind, StateT.bind, peek_run, empty, pure, StateT.pure, Except.bind, Except.pure]
  | @cons input middle first rest head tail ih =>
    obtain ⟨firstFuel, encodedFirst, afterFirst, firstRun, firstCompatible, firstWords,
      _, firstExtension, firstNames⟩ := raw_statement_complete head signature state words
        (wellFormed first List.mem_cons_self) compatible (fresh first List.mem_cons_self)
    have namesUnique : first.name ∉ rest.map NamedFOF.Declaration.name ∧
        (rest.map NamedFOF.Declaration.name).Nodup := by
      simpa only [List.map_cons, List.nodup_cons] using unique
    have tailWellFormed : NamedFOF.ProblemWellFormed signature rest :=
      fun declaration member => wellFormed declaration (List.mem_cons_of_mem first member)
    have tailFresh : ∀ declaration ∈ rest, declaration.name ∉ afterFirst.clauseNames := by
      intro declaration member present
      rw [firstNames] at present
      rcases List.mem_append.mp present with prior | current
      · exact fresh declaration (List.mem_cons_of_mem first member) prior
      · have same : declaration.name = first.name := by simpa using current
        exact namesUnique.1 (List.mem_map.mpr ⟨declaration, member, same⟩)
    obtain ⟨tailFuel, encodedTail, final, tailRun, finalCompatible, finalNames, tailExtension⟩ :=
      ih afterFirst firstWords tailWellFormed namesUnique.2 firstCompatible tailFresh
    let fuel := max firstFuel tailFuel
    have firstLift := statement_fuel_monotone firstFuel fuel (Nat.le_max_left _ _)
      state encodedFirst afterFirst firstRun
    have tailLift := statements_fuel_monotone tailFuel fuel (Nat.le_max_right _ _)
      afterFirst encodedTail final tailRun
    have nonempty : (state.tokens.head?.map Token.text).isNone = false := by
      cases head with
      | cnf grammar => cases grammar; rw [← spellings_head, words]; rfl
      | fof grammar => cases grammar; rw [← spellings_head, words]; rfl
    refine ⟨fuel + 1, encodedFirst :: encodedTail, final, ?_, finalCompatible, ?_,
      firstExtension.trans tailExtension⟩
    · simp [statements, bind, StateT.bind, peek_run, nonempty, firstLift, tailLift,
        pure, StateT.pure, Except.bind, Except.pure]
    · simp only [finalNames, firstNames, List.map_cons, List.append_assoc, List.singleton_append]

theorem decode_complete {input : String} (valid : ValidInput (Source.Grammar.spelling input)) :
    ∃ decoded, decode input = .ok decoded := by
  obtain ⟨named, signature, ⟨raw, lexed, grammar, unique⟩, wellFormed⟩ := valid
  have tokenized := (fof_tokenize_bytes_iff input raw).mpr lexed
  let initial : State := { tokens := raw, endOffset := input.utf8ByteSize }
  have compatible : SignatureCompatible signature initial := by
    simp [SignatureCompatible, TableCompatible, initial]
  obtain ⟨fuel, encoded, final, success, _⟩ := raw_statements_complete grammar signature initial
    rfl wellFormed unique compatible (by simp [initial])
  exact ⟨⟨encoded, final⟩, decode_of_success_at_any_fuel tokenized success⟩

theorem decode_accepts_iff_valid (input : String) :
    (∃ decoded, decode input = .ok decoded) ↔ ValidInput (Source.Grammar.spelling input) := by
  constructor
  · rintro ⟨decoded, success⟩
    exact decode_valid_input success
  · exact decode_complete

theorem decode_complete_named {input : String} {named : List NamedFOF.Declaration}
    (signature : Source.Signature) (parsed : Parses (Source.Grammar.spelling input) named)
    (wellFormed : NamedFOF.ProblemWellFormed signature named) :
    ∃ decoded, decode input = .ok decoded ∧
      NamedFOF.ProblemEncoding (signatureFrom decoded.state) (symbolsFrom decoded.state)
        named decoded.declarations := by
  obtain ⟨decoded, success⟩ := decode_complete ⟨named, signature, parsed, wellFormed⟩
  obtain ⟨actual, actualParse, encoding⟩ := decode_byte_grammar success
  have same := FOFGrammar.Parses.unique parsed actualParse
  refine ⟨decoded, success, ?_⟩
  simpa only [same] using encoding

end Fang.FOFFrontend
