/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import CnfBooleanDeclarationInput

namespace Fang.TptpCandidate.FullFof.CnfBoolean
open Grammar

inductive BodyTokens : List Token → Body → List Token → Prop where
  | fof {input value rest} (formula : FormulaTokens input value rest) : BodyTokens input (.fof value) rest
  | cnf {input values rest} (clause : ClauseTokens input values rest) : BodyTokens input (.cnf values) rest

inductive DeclarationTokens : List Token → Declaration → List Token → Prop where
  | declaration {keyword opening nameToken name nameComma role roleComma bodyInput body closing dot rest endOffset}
      (keywordKind : keyword.kind = .legacy (.lower (BodyKind body)))
      (openParen : Punct opening '(') (recordName : RecordName nameToken name)
      (commaName : Punct nameComma ',') (axiomRole : role.kind = .legacy (.lower "axiom"))
      (commaRole : Punct roleComma ',')
      (parsed : BodyTokens bodyInput body (closing :: dot :: rest))
      (closeParen : Punct closing ')') (period : Punct dot '.') :
      DeclarationTokens (keyword :: opening :: nameToken :: nameComma :: role :: roleComma :: bodyInput)
        ⟨name, body, keyword.start, dot.stop, offset endOffset bodyInput,
          bodyEnd endOffset bodyInput (closing :: dot :: rest)⟩ rest

theorem declaration_sound {seen endOffset input value final}
    (success : declaration seen endOffset input = .ok (value, final)) :
    DeclarationTokens input value final ∧ value.name ∉ seen := by
  cases input with
  | nil => simp [declaration, failure] at success
  | cons keyword rest =>
    simp only [declaration, failure, bind, Except.bind, pure, Except.pure] at success
    repeat' first | contradiction | split at success
    · rename_i _ keywordAt _ opened openAt _ nameToken afterName nameInput
        _ nameKind nameKindAt _ name nameAt fresh _ roleComma roleCommaAt
        _ role afterRole roleInput _ roleAt _ bodyComma bodyCommaAt _
        _ clauseResult clauseAt noAnnotation _ closing closingAt _ dot dotAt
      have openShape := expect_exact openAt
      have roleCommaShape := expect_exact roleCommaAt
      have bodyCommaShape := expect_exact bodyCommaAt
      have closingShape := expect_exact closingAt
      have dotShape := expect_exact dotAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      constructor
      · rw [openShape.1, nameInput, roleCommaShape.1, roleInput, bodyCommaShape.1]
        rw [closingShape.1, dotShape.1]
        apply DeclarationTokens.declaration keywordAt openShape.2
          ⟨nameKind, nameKindAt, nameAt⟩ roleCommaShape.2 roleAt bodyCommaShape.2
        · have parsed := clause_sound clauseAt
          rw [closingShape.1, dotShape.1] at parsed
          exact .cnf parsed
        · exact closingShape.2
        · exact dotShape.2
      · simpa using fresh
    · rename_i _ keywordAt _ opened openAt _ nameToken afterName nameInput
        _ nameKind nameKindAt _ name nameAt fresh _ roleComma roleCommaAt
        _ role afterRole roleInput _ roleAt _ bodyComma bodyCommaAt _
        _ body bodyAt noAnnotation _ closing closingAt _ dot dotAt
      have openShape := expect_exact openAt
      have roleCommaShape := expect_exact roleCommaAt
      have bodyCommaShape := expect_exact bodyCommaAt
      have closingShape := expect_exact closingAt
      have dotShape := expect_exact dotAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      constructor
      · rw [openShape.1, nameInput, roleCommaShape.1, roleInput, bodyCommaShape.1]
        rw [closingShape.1, dotShape.1]
        apply DeclarationTokens.declaration keywordAt openShape.2
          ⟨nameKind, nameKindAt, nameAt⟩ roleCommaShape.2 roleAt bodyCommaShape.2
        · have parsed := formula_sound bodyAt
          rw [closingShape.1, dotShape.1] at parsed
          exact .fof parsed
        · exact closingShape.2
        · exact dotShape.2
      · simpa using fresh

end Fang.TptpCandidate.FullFof.CnfBoolean
