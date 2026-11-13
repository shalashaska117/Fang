/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The CNF clause parser of `CnfBooleanInput` with the parenthesis depth bound as a parameter (option A of
   `roles/bundle/PREMISE-REPLAY.md`): `maxDepth` replaces 64. `clauseAt_accepted` proves it equal to the
   accepted parser at 64, and `clauseAt_sound` proves the accepted clause grammar for every bound. -/
import CnfBooleanGrammar

namespace Fang.TptpCandidate.FullFof.CnfBoolean
open Grammar

def clauseAt (maxDepth : Nat) : Nat → Nat → Nat → List Token → Except Error (List Formula × List Token)
  | 0, _, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, endOffset, tokens => do
    if depth > maxDepth then failure .resource endOffset tokens
    if isChar '(' tokens then
      let (values, rest) ← clauseAt maxDepth fuel (depth + 1) endOffset tokens.tail
      let (_, final) ← expect ')' endOffset rest
      pure (values, final)
    else disjunction (tokens.length + 1) endOffset tokens

theorem clauseAt_accepted_at : ∀ (fuel depth endOffset : Nat) (tokens : List Token),
    clauseAt 64 fuel depth endOffset tokens = clause fuel depth endOffset tokens
  | 0, _, _, _ => by unfold clauseAt clause; rfl
  | fuel + 1, depth, endOffset, tokens => by
    unfold clauseAt clause
    simp only [clauseAt_accepted_at fuel]

theorem clauseAt_accepted : clauseAt 64 = clause := by
  funext fuel depth endOffset tokens
  exact clauseAt_accepted_at fuel depth endOffset tokens

theorem clauseAt_sound {maxDepth fuel depth endOffset input values final}
    (success : clauseAt maxDepth fuel depth endOffset input = .ok (values, final)) :
    ClauseTokens input values final := by
  induction fuel generalizing depth input values final with
  | zero => simp [clauseAt, failure] at success
  | succ fuel ih =>
    simp only [clauseAt, failure, bind, Except.bind, pure, Except.pure] at success
    repeat' first | contradiction | split at success
    · rename_i withinDepth opened _ first firstAt _ closing closingAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      obtain ⟨token, rest, inputShape, kind⟩ := isChar_exact opened
      have closeShape := expect_exact closingAt
      have parsed := ih firstAt
      rw [inputShape] at parsed ⊢
      rw [closeShape.1] at parsed
      exact .paren kind (by simpa using parsed) closeShape.2
    · exact .bare (disjunction_sound success)

#print axioms Fang.TptpCandidate.FullFof.CnfBoolean.clauseAt_accepted_at
#print axioms Fang.TptpCandidate.FullFof.CnfBoolean.clauseAt_accepted
#print axioms Fang.TptpCandidate.FullFof.CnfBoolean.clauseAt_sound

end Fang.TptpCandidate.FullFof.CnfBoolean
