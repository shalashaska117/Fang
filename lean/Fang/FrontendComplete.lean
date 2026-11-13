/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Acceptance of the independent valid-input language by the actual decoder.
Validity includes consistent symbol arities and unique clause names.
-/
import Fang.FrontendStatementComplete
import Fang.FrontendSoundness
import Fang.FrontendFuelBound
import Fang.SourceConsumption

namespace Fang.Frontend

open Source.Grammar

def StatementsCompletion (signature : Source.Signature) (state : State)
    (named : Source.Problem) : Prop :=
  ∃ fuel encoded updated, statements fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧
    updated.clauseNames = state.clauseNames ++ named.map Source.Clause.name ∧
    SymbolExtension state updated

theorem statements_complete {input named} (parsed : ProblemTokens input named)
    (signature : Source.Signature) (state : State)
    (classified : ClassifiedTokens state.tokens input)
    (wellFormed : named.WellFormed signature)
    (compatible : SignatureCompatible signature state)
    (fresh : ∀ clause ∈ named, clause.name ∉ state.clauseNames) :
    StatementsCompletion signature state named := by
  induction parsed generalizing state with
  | empty =>
      have empty : state.tokens = [] := by
        cases shape : state.tokens with
        | nil => rfl
        | cons first rest => rw [shape] at classified; cases classified
      exact ⟨1, [], state, by simp [statements_run, empty], compatible,
        by simp, .refl state⟩
  | @statement input first middle rest head tail induction =>
      obtain ⟨firstFuel, encodedFirst, afterFirst, firstRun, firstCompatible,
        firstClass, _, firstExtension, firstNames⟩ :=
        statement_complete head signature state classified
          (wellFormed.2 first List.mem_cons_self) compatible
          (fresh first List.mem_cons_self)
      have namesUnique : first.name ∉ rest.map Source.Clause.name ∧
          (rest.map Source.Clause.name).Nodup := by
        simpa only [List.map_cons, List.nodup_cons] using wellFormed.1
      have tailWellFormed : rest.WellFormed signature :=
        ⟨namesUnique.2, fun clause member => wellFormed.2 clause
          (List.mem_cons_of_mem first member)⟩
      have tailFresh : ∀ clause ∈ rest, clause.name ∉ afterFirst.clauseNames := by
        intro clause member present
        rw [firstNames] at present
        rcases List.mem_append.mp present with prior | current
        · exact fresh clause (List.mem_cons_of_mem first member) prior
        · have same : clause.name = first.name := by simpa using current
          exact namesUnique.1 (List.mem_map.mpr ⟨clause, member, same⟩)
      obtain ⟨tailFuel, encodedTail, final, tailRun, finalCompatible, finalNames,
        tailExtension⟩ := induction afterFirst firstClass tailWellFormed firstCompatible tailFresh
      let fuel := max firstFuel tailFuel
      have firstRun' := statement_fuel_monotone firstFuel fuel (Nat.le_max_left _ _)
        state encodedFirst afterFirst firstRun
      have tailRun' := statements_fuel_monotone tailFuel fuel (Nat.le_max_right _ _)
        afterFirst encodedTail final tailRun
      have nonempty : state.tokens.isEmpty = false := by
        cases head
        obtain ⟨raw, raws, shape, _, _⟩ := classified.cons_parts
        simp [shape]
      refine ⟨fuel + 1, encodedFirst :: encodedTail, final, ?_, finalCompatible,
        ?_, firstExtension.trans tailExtension⟩
      · rw [statements_run]
        simp [nonempty, firstRun', tailRun', bind, Except.bind, pure, Except.pure]
      · simp only [finalNames, firstNames, List.map_cons, List.append_assoc,
          List.singleton_append]

end Fang.Frontend

namespace Fang

open Frontend Source.Grammar

theorem decode_with_signature_complete {input : String}
    (valid : Source.Grammar.ValidInput (spelling input)) :
    ∃ decoded, decodeProblemWithSignature input = .ok decoded := by
  obtain ⟨named, signature, parsed, wellFormed⟩ := valid
  obtain ⟨raw, tokens, tokenized, classified, grammar⟩ :=
    (grammar_parses_iff_tokenized input named).mp parsed
  let initial : State := { tokens := raw, endOffset := input.utf8ByteSize }
  have compatible : SignatureCompatible signature initial := by
    simp [SignatureCompatible, TableCompatible, initial]
  obtain ⟨fuel, encoded, final, success, _⟩ := statements_complete grammar signature initial
    classified wellFormed compatible (by simp [initial])
  have sufficient := statements_token_count_fuel success
  refine ⟨DecodedProblem.mk encoded
    (final.functions.map (fun symbol => symbol.arity.getD 0))
    (final.predicates.map (fun symbol => symbol.arity.getD 0)), ?_⟩
  simp only [initial] at sufficient
  simp [decodeProblemWithSignature, tokenized, sufficient, bind, Except.bind,
    pure, Except.pure]

theorem decode_complete {input : String}
    (valid : Source.Grammar.ValidInput (spelling input)) :
    ∃ encoded, decodeProblem input = .ok encoded := by
  obtain ⟨decoded, success⟩ := decode_with_signature_complete valid
  exact ⟨decoded.problem, by simp [decodeProblem, success, bind, Except.bind,
    pure, Except.pure]⟩

theorem decode_accepts_iff_valid (input : String) :
    (∃ encoded, decodeProblem input = .ok encoded) ↔
      Source.Grammar.ValidInput (spelling input) := by
  constructor
  · rintro ⟨encoded, success⟩
    obtain ⟨named, final, parsed, encoding⟩ := decode_sound success
    exact Source.Grammar.validInput_of_encoding parsed encoding
  · exact decode_complete

#print axioms Frontend.statements_complete
#print axioms decode_with_signature_complete
#print axioms decode_complete
#print axioms decode_accepts_iff_valid

end Fang
