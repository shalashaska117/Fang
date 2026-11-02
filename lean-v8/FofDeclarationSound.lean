/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import FofDeclarationGrammar

namespace Fang.TptpCandidate
deriving instance ReflBEq, LawfulBEq for Name
namespace FullFof
open Grammar

theorem cnfLiteral_sound {endOffset input value final}
    (success : cnfLiteral endOffset input = .ok (value, final)) :
    CnfLiteralTokens input value final := by
  unfold cnfLiteral at success
  simp only [failure, bind, Except.bind, pure, Except.pure] at success
  repeat' first | contradiction | split at success
  · rename_i negative notQuantified _ result call _ name args shape
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
    obtain ⟨token, rest, inputShape, kind⟩ := isChar_exact negative
    have parsed := atom_sound call
    rw [shape, inputShape] at parsed ⊢
    exact .negative kind (by simpa using parsed)
  · rename_i notNegative notQuantified _ result call
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
    exact .positive (atom_sound call)

theorem cnfLiterals_sound {fuel endOffset input values final}
    (success : cnfLiterals fuel endOffset input = .ok (values, final)) :
    CnfLiteralsTokens input values final := by
  induction fuel generalizing input values final with
  | zero => simp [cnfLiterals, failure] at success
  | succ fuel ih =>
    simp only [cnfLiterals, failure, bind, Except.bind, pure, Except.pure] at success
    repeat' first | contradiction | split at success
    · rename_i _ first firstAt bar _ tail tailAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      obtain ⟨separator, rest, shape, separatorAt⟩ := isChar_exact bar
      have parsed := cnfLiteral_sound firstAt
      rw [shape] at parsed tailAt
      exact .more parsed separatorAt (ih (by simpa using tailAt))
    · rename_i _ first firstAt notBar notOther
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      exact .one (cnfLiteral_sound firstAt) (by simpa using notBar)

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
        _ bodyOpen bodyOpenAt _ falseToken afterFalse falseInput _ falseAt
        _ bodyClose bodyCloseAt noAnnotation _ closing closingAt _ dot dotAt
      have openShape := expect_exact openAt
      have roleCommaShape := expect_exact roleCommaAt
      have bodyCommaShape := expect_exact bodyCommaAt
      have bodyOpenShape := expect_exact bodyOpenAt
      have bodyCloseShape := expect_exact bodyCloseAt
      have closingShape := expect_exact closingAt
      have dotShape := expect_exact dotAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      constructor
      · rw [openShape.1, nameInput, roleCommaShape.1, roleInput, bodyCommaShape.1]
        rw [closingShape.1, dotShape.1]
        apply DeclarationTokens.declaration keywordAt openShape.2
          ⟨nameKind, nameKindAt, nameAt⟩ roleCommaShape.2 roleAt bodyCommaShape.2
        · rw [bodyOpenShape.1, falseInput, bodyCloseShape.1, closingShape.1, dotShape.1]
          exact .cnfFalse bodyOpenShape.2 falseAt bodyCloseShape.2
        · exact closingShape.2
        · exact dotShape.2
      · simpa using fresh
    · rename_i _ keywordAt _ opened openAt _ nameToken afterName nameInput
        _ nameKind nameKindAt _ name nameAt fresh _ roleComma roleCommaAt
        _ role afterRole roleInput _ roleAt _ bodyComma bodyCommaAt _
        _ bodyOpen bodyOpenAt _ firstToken afterFirst firstInput _ notFalse notTrue
        _ clauseResult clauseAt _ bodyClose bodyCloseAt noAnnotation
        _ closing closingAt _ dot dotAt
      have openShape := expect_exact openAt
      have roleCommaShape := expect_exact roleCommaAt
      have bodyCommaShape := expect_exact bodyCommaAt
      have bodyOpenShape := expect_exact bodyOpenAt
      have bodyCloseShape := expect_exact bodyCloseAt
      have closingShape := expect_exact closingAt
      have dotShape := expect_exact dotAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      constructor
      · rw [openShape.1, nameInput, roleCommaShape.1, roleInput, bodyCommaShape.1]
        rw [closingShape.1, dotShape.1]
        apply DeclarationTokens.declaration keywordAt openShape.2
          ⟨nameKind, nameKindAt, nameAt⟩ roleCommaShape.2 roleAt bodyCommaShape.2
        · rw [bodyOpenShape.1]
          apply BodyTokens.cnf bodyOpenShape.2
          · have parsed := cnfLiterals_sound clauseAt
            rwa [bodyCloseShape.1, closingShape.1, dotShape.1] at parsed
          · exact bodyCloseShape.2
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

end FullFof
end Fang.TptpCandidate
