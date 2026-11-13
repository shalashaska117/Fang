/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The record decoder `CnfBoolean.declaration` with the formula height bound as a parameter (option A of
   `roles/bundle/PREMISE-REPLAY.md`), the declaration-level interface agreed with worker-roles:
   `declarationD maxDepth` takes the arguments of `declaration` after `maxDepth`, `declarationD_accepted` proves
   it equal to `declaration` at 64, and `declarationD_sound` and `declarationD_closed` give the conclusions of
   `declaration_sound` and `declaration_closed` for every bound. Term depth stays 64. -/
import CnfBooleanDeclarationSound
import CnfBooleanInputDepth
import FofInputDepthSound

namespace Fang.TptpCandidate.FullFof.CnfBoolean
open Grammar

def declarationD (maxDepth : Nat) (seen : List Name) (endOffset : Nat) (tokens : List Token) :
    Except Error (Declaration × List Token) := do
  let keyword :: rest := tokens | failure .invalid endOffset tokens
  let isCnf ← match keyword.kind with
    | .legacy (.lower "cnf") => pure true
    | .legacy (.lower "fof") => pure false
    | .legacy (.lower "include") | .legacy (.lower "tff") | .legacy (.lower "thf") |
        .legacy (.lower "tcf") => failure .unsupported endOffset tokens
    | _ => failure .invalid endOffset tokens
  let (_, rest) ← expect '(' endOffset rest
  let nameToken :: rest := rest | failure .invalid endOffset rest
  let .legacy nameKind := nameToken.kind | failure .invalid endOffset (nameToken :: rest)
  let some name := nameKind.name | failure .invalid endOffset (nameToken :: rest)
  if seen.contains name then failure .invalid endOffset (nameToken :: rest)
  let (_, rest) ← expect ',' endOffset rest
  let role :: rest := rest | failure .invalid endOffset rest
  match role.kind with
  | .legacy (.lower "axiom") => pure ()
  | .legacy (.lower _) => failure .unsupported endOffset (role :: rest)
  | _ => failure .invalid endOffset (role :: rest)
  let (_, originalBody) ← expect ',' endOffset rest
  let (body, rest) ← if isCnf then do
      let (values, rest) ← clauseAt maxDepth (originalBody.length + 1) 1 endOffset originalBody
      pure (Body.cnf values, rest)
    else do
      let (body, rest) ← formulaAt maxDepth (3 * originalBody.length + 1) 1 [] endOffset originalBody
      pure (Body.fof body, rest)
  let bodyStop := ((originalBody.take (originalBody.length - rest.length)).getLast?.map Token.stop).getD endOffset
  if isChar ',' rest then failure .unsupported endOffset rest
  let (_, rest) ← expect ')' endOffset rest
  let (dot, rest) ← expect '.' endOffset rest
  pure (⟨name, body, keyword.start, dot.stop, offset endOffset originalBody, bodyStop⟩, rest)

theorem declarationD_accepted : declarationD 64 = declaration := by
  funext seen endOffset tokens
  unfold declarationD declaration
  simp only [clauseAt_accepted, formulaAt_accepted]
  rfl

theorem declarationD_sound {maxDepth seen endOffset input value final}
    (success : declarationD maxDepth seen endOffset input = .ok (value, final)) :
    DeclarationTokens input value final ∧ value.name ∉ seen := by
  cases input with
  | nil => simp [declarationD, failure] at success
  | cons keyword rest =>
    simp only [declarationD, failure, bind, Except.bind, pure, Except.pure] at success
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
        · have parsed := clauseAt_sound clauseAt
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
        · have parsed := formulaAt_sound bodyAt
          rw [closingShape.1, dotShape.1] at parsed
          exact .fof parsed
        · exact closingShape.2
        · exact dotShape.2
      · simpa using fresh

theorem declarationD_closed {maxDepth seen endOffset input value final}
    (success : declarationD maxDepth seen endOffset input = .ok (value, final)) :
    match value.body with | .cnf _ => True | .fof body => body.Within [] := by
  cases input with
  | nil => simp [declarationD, failure] at success
  | cons keyword rest =>
    simp only [declarationD, failure, bind, Except.bind, pure, Except.pure] at success
    repeat' first | contradiction | split at success
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success); trivial
    · rename_i _ keywordAt _ opened openAt _ nameToken afterName nameInput
        _ nameKind nameKindAt _ name nameAt fresh _ roleComma roleCommaAt
        _ role afterRole roleInput _ roleAt _ bodyComma bodyCommaAt _
        _ body bodyAt noAnnotation _ closing closingAt _ dot dotAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      exact formulaAt_within bodyAt

#print axioms Fang.TptpCandidate.FullFof.CnfBoolean.declarationD_accepted
#print axioms Fang.TptpCandidate.FullFof.CnfBoolean.declarationD_sound
#print axioms Fang.TptpCandidate.FullFof.CnfBoolean.declarationD_closed

end Fang.TptpCandidate.FullFof.CnfBoolean
