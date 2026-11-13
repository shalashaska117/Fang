/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The signed role decoder with counted parsing. The role decoder calls `Integration.declarationC` with the token count in place of the accepted `CnfBoolean.declaration`, and the byte decoder uses the linear lexer; both are proved equal to the accepted role decoder. The signed version-8 entries over the linear decoder are equal to the accepted ones, so their theorems carry over. -/
import SignedEnvelope
import ExpandedDecoder

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Bytes
open FullFof

theorem header_patched_length {tokens : List FullFof.Token} {header : Header} (found : header? tokens = some header) :
    header.patched.length = tokens.length := by
  unfold header? at found
  split at found
  · cases found
    simp [Header.patched]
  · cases found

/-- `declaration` with the count of `tokens` carried beside them. -/
def declarationC (seen : List Name) (endOffset : Nat) (tokens : List FullFof.Token) (count : Nat) :
    Except Error (Entry × List FullFof.Token × Nat) := do
  let some header := header? tokens | FullFof.failure .invalid endOffset tokens
  let role ← readRole endOffset header.role
  if invalidGoal header role then FullFof.failure .invalid endOffset tokens
  let (original, rest, restCount) ← Integration.declarationC seen endOffset header.patched count
  pure (⟨original, role, header.role.start, header.role.stop⟩, rest, restCount)

theorem declarationC_eq {seen endOffset tokens count} (counted : count = tokens.length) :
    declarationC seen endOffset tokens count = (declaration seen endOffset tokens).map Integration.annotate := by
  unfold declarationC declaration
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
        rw [Integration.declarationC_eq (count := count) (by rw [counted, header_patched_length found])]
        cases CnfBoolean.declaration seen endOffset header.patched with
        | error problem => rfl
        | ok pair => rfl

/-- `declarations` with the count carried beside the tokens. -/
def declarationsC : Nat → List Name → Nat → List FullFof.Token → Nat → Except Error (List Entry)
  | 0, _, endOffset, tokens, _ => FullFof.failure .resource endOffset tokens
  | _ + 1, _, _, [], _ => .ok []
  | fuel + 1, seen, endOffset, tokens@(_ :: _), count => do
    if seen.length ≥ 1000 then FullFof.failure .resource endOffset tokens
    let (first, rest, restCount) ← declarationC seen endOffset tokens count
    let tail ← declarationsC fuel (first.original.name :: seen) endOffset rest restCount
    pure (first :: tail)

theorem declarationsC_eq : ∀ fuel seen endOffset tokens count, count = tokens.length →
    declarationsC fuel seen endOffset tokens count = declarations fuel seen endOffset tokens
  | 0, _, _, _, _, _ => by
    unfold declarationsC declarations
    rfl
  | fuel + 1, seen, endOffset, [], _, _ => by
    unfold declarationsC declarations
    rfl
  | fuel + 1, seen, endOffset, token :: rest, count, counted => by
    unfold declarationsC declarations
    by_cases full : seen.length ≥ 1000
    · simp only [full, ↓reduceIte]
      rfl
    · simp only [full, ↓reduceIte]
      rw [declarationC_eq counted, Integration.bind_annotate]
      apply Integration.bind_congr_ok
      intro value _
      simp only [Integration.annotate]
      rw [declarationsC_eq fuel (value.1.original.name :: seen) endOffset value.2 value.2.length rfl]

/-- The role byte decoder with the linear lexer and counted parsing. -/
def decodeBytesLinear (input : List UInt8) (maximumBytes : Nat := 1048576) : Except Error (List Entry) := do
  let tokens ← Integration.fastTokenizeBytes input maximumBytes
  let values ← declarationsC (tokens.length + 1) [] input.length tokens tokens.length
  if modesValid values then pure values else FullFof.failure .unsupported input.length []

/-- The linear role decoder returns exactly what the accepted role decoder returns. -/
theorem decodeBytesLinear_eq (input : List UInt8) (maximumBytes : Nat) :
    decodeBytesLinear input maximumBytes = decodeBytes input maximumBytes := by
  unfold decodeBytesLinear decodeBytes
  rw [Integration.fastTokenizeBytes_eq]
  cases FullFof.tokenizeBytes input maximumBytes with
  | error problem => rfl
  | ok tokens =>
    simp only [Bind.bind, Except.bind]
    rw [declarationsC_eq _ [] input.length tokens tokens.length rfl]

end Fang.TptpCandidate.Roles.Bytes

namespace Fang.TptpCandidate.Roles.Signed
open FullFof Numeric

/-- `decodeSigned` over the linear role decoder. -/
def decodeSignedLinear (bytes : List UInt8) (maximumBytes : Nat) :
    Except SignedError (List Bytes.Entry × SignedInput) := do
  let values ← (Bytes.decodeBytesLinear bytes maximumBytes).mapError .input
  match readSigned values with
  | none => .error .nonliteral
  | some input => .ok (values, input)

theorem decodeSignedLinear_eq (bytes : List UInt8) (maximumBytes : Nat) :
    decodeSignedLinear bytes maximumBytes = decodeSigned bytes maximumBytes := by
  unfold decodeSignedLinear decodeSigned
  rw [Bytes.decodeBytesLinear_eq]
  rfl

def prepareGoalLinear (bytes : List UInt8) (maximumBytes index : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except SignedError GoalPrepared := do
  let (_, input) ← decodeSignedLinear bytes maximumBytes
  let some (before, goal, after) := (goalSplits input)[index]? | .error .noGoal
  let some task := goalTask before goal after | .error .cnfGoal
  let replay ← replayTask input task limits maximumPredicates maximumLiterals
  pure ⟨goal.declaration, replay⟩

def prepareInputsLinear (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) : Except SignedError SignedPrepared := do
  let decoded ← decodeSignedLinear bytes maximumBytes
  if (goalSplits decoded.2).isEmpty then
    replayTask decoded.2 (inputsTask decoded.2) limits maximumPredicates maximumLiterals
  else .error .goalsPresent

theorem prepareGoalLinear_eq (bytes : List UInt8) (maximumBytes index : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    prepareGoalLinear bytes maximumBytes index limits maximumPredicates maximumLiterals =
      prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals := by
  unfold prepareGoalLinear prepareGoal
  rw [decodeSignedLinear_eq]
  rfl

theorem prepareInputsLinear_eq (bytes : List UInt8) (maximumBytes : Nat) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    prepareInputsLinear bytes maximumBytes limits maximumPredicates maximumLiterals =
      prepareInputs bytes maximumBytes limits maximumPredicates maximumLiterals := by
  unfold prepareInputsLinear prepareInputs
  rw [decodeSignedLinear_eq]

/-- `acceptsGoal` over the linear role decoder. -/
def acceptsGoalLinear (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except SignedAcceptError Unit := do
  let prepared ← (prepareGoalLinear bytes maximumBytes index limits maximumPredicates maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate

/-- `acceptsInputs` over the linear role decoder. -/
def acceptsInputsLinear (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except SignedAcceptError Unit := do
  let prepared ← (prepareInputsLinear bytes maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities
    prepared.predicateArities proof).mapError .certificate

theorem acceptsGoalLinear_eq (bytes : List UInt8) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsGoalLinear bytes maximumBytes index proof limits maximumPredicates maximumLiterals =
      acceptsGoal bytes maximumBytes index proof limits maximumPredicates maximumLiterals := by
  unfold acceptsGoalLinear acceptsGoal
  rw [prepareGoalLinear_eq]

theorem acceptsInputsLinear_eq (bytes : List UInt8) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsInputsLinear bytes maximumBytes proof limits maximumPredicates maximumLiterals =
      acceptsInputs bytes maximumBytes proof limits maximumPredicates maximumLiterals := by
  unfold acceptsInputsLinear acceptsInputs
  rw [prepareInputsLinear_eq]

/-- Acceptance of one goal's certificate over the linear decoder proves what `acceptsGoal_entails` proves. -/
theorem acceptsGoalLinear_entails {bytes maximumBytes index proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsGoalLinear bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoal bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      ∃ values, Bytes.ByteParsed bytes maximumBytes values ∧ Bytes.Closed values ∧
        prepared.goal ∈ Roles.goals (Bytes.source values) ∧
        ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
            Bytes.sentence model prepared.goal.original := by
  rw [acceptsGoalLinear_eq] at accepted
  exact acceptsGoal_entails accepted

/-- Theorem endpoint over the linear decoder: at least one original conjecture, and an accepted certificate for each one. -/
theorem acceptsGoalsLinear_theorem {bytes maximumBytes values limits maximumPredicates maximumLiterals}
    (decoded : Bytes.decodeBytesLinear bytes maximumBytes = .ok values)
    (nonempty : Roles.goals (Bytes.source values) ≠ [])
    (accepted : ∀ goal ∈ Roles.goals (Bytes.source values), ∃ index prepared proof,
      prepareGoalLinear bytes maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared ∧
      prepared.goal = goal ∧
      acceptsGoalLinear bytes maximumBytes index proof limits maximumPredicates maximumLiterals = .ok ()) :
    BytesTheorem bytes maximumBytes := by
  rw [Bytes.decodeBytesLinear_eq] at decoded
  apply acceptsGoals_theorem decoded nonempty
  intro goal member
  obtain ⟨index, prepared, proof, run, same, checked⟩ := accepted goal member
  rw [prepareGoalLinear_eq] at run
  rw [acceptsGoalLinear_eq] at checked
  exact ⟨index, prepared, proof, run, same, checked⟩

/-- Acceptance of the no-goal task's certificate over the linear decoder proves that the accepted positive inputs are unsatisfiable. -/
theorem acceptsInputsLinear_unsat {bytes maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsInputsLinear bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximumBytes := by
  rw [acceptsInputsLinear_eq] at accepted
  exact acceptsInputs_unsat accepted

end Fang.TptpCandidate.Roles.Signed

#print axioms Fang.TptpCandidate.Roles.Bytes.header_patched_length
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationC_eq
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsC_eq
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeBytesLinear_eq
#print axioms Fang.TptpCandidate.Roles.Signed.decodeSignedLinear_eq
#print axioms Fang.TptpCandidate.Roles.Signed.prepareGoalLinear_eq
#print axioms Fang.TptpCandidate.Roles.Signed.prepareInputsLinear_eq
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoalLinear_eq
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsInputsLinear_eq
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoalLinear_entails
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoalsLinear_theorem
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsInputsLinear_unsat
