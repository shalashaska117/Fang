/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Role declaration decoding with a formula-depth parameter and unchanged grammar. -/
import RoleDecoderLimit
import ExpandedDecoderDepth

namespace Fang.TptpCandidate.Roles.Bytes
open FullFof

def declarationD (maxDepth : Nat) (seen : List Name) (endOffset : Nat) (tokens : List FullFof.Token) :
    Except Error (Entry × List FullFof.Token) := do
  let some header := header? tokens | FullFof.failure .invalid endOffset tokens
  let role ← readRole endOffset header.role
  if invalidGoal header role then FullFof.failure .invalid endOffset tokens
  let (original, rest) ← CnfBoolean.declarationD maxDepth seen endOffset header.patched
  pure (⟨original, role, header.role.start, header.role.stop⟩, rest)

theorem declarationD_witness {maxDepth seen endOffset tokens value final}
    (success : declarationD maxDepth seen endOffset tokens = .ok (value, final)) :
    ∃ header, tokens = header.tokens ∧
      readRole endOffset header.role = .ok value.role ∧ invalidGoal header value.role = false ∧
      CnfBoolean.declarationD maxDepth seen endOffset header.patched = .ok (value.original, final) ∧
      value.roleStart = header.role.start ∧ value.roleStop = header.role.stop := by
  unfold declarationD at success
  cases headerAt : header? tokens with
  | none => simp [headerAt, FullFof.failure] at success
  | some header =>
    cases roleAt : readRole endOffset header.role with
    | error reason => simp [headerAt, roleAt, bind, Except.bind] at success
    | ok role =>
      cases valid : invalidGoal header role with
      | true => simp [headerAt, roleAt, valid, bind, Except.bind, FullFof.failure] at success
      | false =>
        cases resultAt : CnfBoolean.declarationD maxDepth seen endOffset header.patched with
        | error reason => simp [headerAt, roleAt, valid, resultAt, bind, Except.bind] at success
        | ok result =>
          rcases result with ⟨original, rest⟩
          have same : (⟨original, role, header.role.start, header.role.stop⟩, rest) = (value, final) := by
            simpa [headerAt, roleAt, valid, resultAt, bind, Except.bind, pure, Except.pure] using success
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
          exact ⟨header, header_exact headerAt, roleAt, valid, resultAt, rfl, rfl⟩

theorem declarationD_sound {maxDepth seen endOffset tokens value final}
    (success : declarationD maxDepth seen endOffset tokens = .ok (value, final)) :
    DeclarationTokens tokens value final ∧ value.original.name ∉ seen := by
  obtain ⟨header, shape, roleAt, valid, originalAt, start, stop⟩ := declarationD_witness success
  have original := CnfBoolean.declarationD_sound originalAt
  constructor
  · have same : value = ⟨value.original, value.role, header.role.start, header.role.stop⟩ := by
      cases value
      simp_all
    rw [shape, same]
    exact .declaration (readRole_sound roleAt) valid original.1
  · exact original.2

theorem declarationD_closed {maxDepth seen endOffset tokens value final}
    (success : declarationD maxDepth seen endOffset tokens = .ok (value, final)) :
    match value.original.body with | .cnf _ => True | .fof body => body.Within [] := by
  obtain ⟨_, _, _, _, original, _, _⟩ := declarationD_witness success
  exact CnfBoolean.declarationD_closed original

def declarationCD (maxDepth : Nat) (seen : List Name) (endOffset : Nat) (tokens : List FullFof.Token) (count : Nat) :
    Except Error (Entry × List FullFof.Token × Nat) := do
  let some header := header? tokens | FullFof.failure .invalid endOffset tokens
  let role ← readRole endOffset header.role
  if invalidGoal header role then FullFof.failure .invalid endOffset tokens
  let (original, rest, restCount) ← Integration.declarationCD maxDepth seen endOffset header.patched count
  pure (⟨original, role, header.role.start, header.role.stop⟩, rest, restCount)

theorem declarationCD_eq {maxDepth seen endOffset tokens count} (counted : count = tokens.length) :
    declarationCD maxDepth seen endOffset tokens count = (declarationD maxDepth seen endOffset tokens).map Integration.annotate := by
  unfold declarationCD declarationD
  cases found : header? tokens with
  | none => rfl
  | some header =>
    simp only
    cases roleRun : readRole endOffset header.role with
    | error problem => rfl
    | ok role =>
      simp only [Bind.bind, Except.bind]
      by_cases bad : invalidGoal header role = true
      · simp only [bad, ↓reduceIte]
        rfl
      · simp only [bad, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
        rw [Integration.declarationCD_eq (count := count) (by rw [counted, header_patched_length found])]
        cases CnfBoolean.declarationD maxDepth seen endOffset header.patched with
        | error problem => rfl
        | ok pair => rfl

def declarationSeenCD (maxDepth : Nat) (isSeen : Name → Bool) (endOffset : Nat)
    (tokens : List FullFof.Token) (count : Nat) : Except Error (Entry × List FullFof.Token × Nat) := do
  let some header := header? tokens | FullFof.failure .invalid endOffset tokens
  let role ← readRole endOffset header.role
  if invalidGoal header role then FullFof.failure .invalid endOffset tokens
  let (original, rest, restCount) ← Integration.declarationSeenCD maxDepth isSeen endOffset header.patched count
  pure (⟨original, role, header.role.start, header.role.stop⟩, rest, restCount)

theorem declarationSeenCD_eq {maxDepth : Nat} {isSeen : Name → Bool} {seen : List Name}
    (same : ∀ label, isSeen label = seen.contains label) (endOffset : Nat) (tokens : List FullFof.Token) (count : Nat) :
    declarationSeenCD maxDepth isSeen endOffset tokens count = declarationCD maxDepth seen endOffset tokens count := by
  unfold declarationSeenCD declarationCD
  simp only [Integration.declarationSeenCD_eq same]

theorem declarationD_accepted : declarationD 64 = declaration := by
  funext seen endOffset tokens
  unfold declarationD declaration
  rw [CnfBoolean.declarationD_accepted]
  rfl

theorem declarationCD_accepted : declarationCD 64 = declarationC := by
  funext seen endOffset tokens count
  unfold declarationCD declarationC
  rw [Integration.declarationCD_accepted]
  rfl

theorem declarationSeenCD_accepted : declarationSeenCD 64 = declarationSeenC := by
  funext seen endOffset tokens count
  unfold declarationSeenCD declarationSeenC
  rw [Integration.declarationSeenCD_accepted]
  rfl

theorem declarationD_goal_fof {maxDepth seen endOffset tokens value final}
    (success : declarationD maxDepth seen endOffset tokens = .ok (value, final))
    (goal : value.role = .conjecture) : ∃ formula, value.original.body = .fof formula := by
  obtain ⟨header, _, _, valid, originalAt, _, _⟩ := declarationD_witness success
  obtain ⟨keyword, more, shape, kind⟩ := Signed.grammar_keyword (CnfBoolean.declarationD_sound originalAt).1
  simp only [Header.patched, List.cons.injEq] at shape
  obtain ⟨rfl, -⟩ := shape
  simp only [invalidGoal, goal, decide_true, Bool.true_and] at valid
  cases bodyShape : value.original.body with
  | fof formula => exact ⟨formula, rfl⟩
  | cnf literals =>
    rw [bodyShape] at kind
    rw [kind] at valid
    simp only [FullFof.Grammar.BodyKind] at valid
    exact absurd valid (by decide)

end Fang.TptpCandidate.Roles.Bytes
