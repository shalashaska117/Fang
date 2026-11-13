/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Arity checks for represented source occurrences after the actual getD-0 export.
Unknown, unused table slots are outside these occurrence-specific contracts.
-/
import Fang.FrontendTableEncoding
import Fang.CertificateInput

namespace Fang.Frontend

def exportedArities (symbols : List Symbol) : List Nat :=
  symbols.map (fun symbol => symbol.arity.getD 0)

def exportedProblem (state : State) (problem : Fang.Problem) : DecodedProblem where
  problem
  functionArities := exportedArities state.functions
  predicateArities := exportedArities state.predicates

theorem export_signature_known {symbols : List Symbol} {id arity : Nat}
    (checked : (symbols[id]?).map Symbol.arity = some (some arity)) :
    (exportedArities symbols)[id]? = some arity := by
  cases entry : symbols[id]? with
  | none => simp [entry] at checked
  | some symbol =>
      simp only [entry, Option.map_some, Option.some.injEq] at checked
      simp [exportedArities, List.getElem?_map, entry, checked]

mutual
theorem TableTermEncoding.export_wellFormed {state named encoded}
    (encoding : TableTermEncoding state named encoded) :
    Fang.termWellFormed (exportedArities state.functions) encoded = true := by
  cases encoding with
  | var => rfl
  | app name id arguments terms found checked children =>
      have arity := export_signature_known checked
      rw [children.length] at arity
      simp [Fang.termWellFormed, arity, children.export_wellFormed]

theorem TableTermsEncoding.export_wellFormed {state named encoded}
    (encoding : TableTermsEncoding state named encoded) :
    Fang.termsWellFormed (exportedArities state.functions) encoded = true := by
  cases encoding with
  | nil => rfl
  | cons head tail =>
      simp [Fang.termsWellFormed, head.export_wellFormed, tail.export_wellFormed]
end

theorem TableLiteralEncoding.export_wellFormed {state named encoded}
    (encoding : TableLiteralEncoding state named encoded) :
    ((exportedArities state.predicates)[encoded.atom.pred]? == some encoded.atom.args.length &&
      Fang.termsWellFormed (exportedArities state.functions) encoded.atom.args) = true := by
  have arity := export_signature_known encoding.checked
  rw [encoding.arguments.length] at arity
  simp [arity, encoding.arguments.export_wellFormed]

theorem tableClause_export_wellFormed {state named encoded}
    (encoding : Source.RelatedLists (TableLiteralEncoding state) named encoded)
    (problem : Fang.Problem) :
    Fang.clauseWellFormed (exportedProblem state problem) encoded = true := by
  induction encoding with
  | nil => rfl
  | cons head tail induction =>
      simp only [Fang.clauseWellFormed, List.all_cons, exportedProblem] at induction ⊢
      simp only [head.export_wellFormed, induction, Bool.and_self]

theorem decodeProblemWithSignature_exported {input : String} {decoded : DecodedProblem}
    (success : decodeProblemWithSignature input = .ok decoded) :
    ∃ tokens state,
      tokenize input = .ok tokens ∧
      statements (tokens.length + 1) { tokens, endOffset := input.utf8ByteSize } =
        .ok (decoded.problem, state) ∧
      decoded = exportedProblem state decoded.problem := by
  obtain ⟨tokens, state, tokenized, parsed, _, _, functions, predicates⟩ :=
    Fang.decodeProblemWithSignature_success success
  refine ⟨tokens, state, tokenized, parsed, ?_⟩
  cases decoded
  simp only [exportedProblem, exportedArities, DecodedProblem.mk.injEq, true_and]
  exact ⟨functions, predicates⟩

#print axioms export_signature_known
#print axioms TableTermEncoding.export_wellFormed
#print axioms TableTermsEncoding.export_wellFormed
#print axioms TableLiteralEncoding.export_wellFormed
#print axioms tableClause_export_wellFormed
#print axioms decodeProblemWithSignature_exported

end Fang.Frontend
