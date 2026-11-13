/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The revision-2 role framer with the linear framer lexer, the reversed statement splitter and the counted role record decoder. Each fast function is proved equal to the gated one, so the fast read, replay and version-8 entries are the revision-2 entries with the gated tokenizer, and their theorems follow by rewriting. -/
import RoleReplayV2
import SignedLinear
import BundleFastLexer

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Bundle.V2
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-! The framer. -/

/-- The linear revision-2 lexer as a role-framer tokenizer. -/
def fast : Tokenizer := Coverage.FramerV2.tokenizeFast

theorem fast_eq_gated (bytes : List UInt8) (maximum : Nat) : fast bytes maximum = gated bytes maximum :=
  Coverage.FramerV2.tokenizeFast_eq bytes maximum

/-- Through `frameBundle_congr`: the role framer with the linear lexer alone is the gated role framer. -/
theorem frameBundle_fast : frameBundle fast = frameBundle gated := frameBundle_congr fast_eq_gated

/-- `formulaRecord` with the counted role record decoder. -/
def formulaRecordFast (seen : List Name) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    Except Error Bytes.Entry :=
  match Coverage.FramerV2.nameGuard pieces with
  | .error problem => .error problem
  | .ok () =>
    let tokens := (Coverage.FramerV2.cutRecord pieces).1.map Coverage.FramerV2.coreToken
    match Bytes.declarationC seen endOffset tokens tokens.length with
    | .error problem => .error problem
    | .ok (value, rest, _) =>
      if !rest.isEmpty then .error ⟨.invalid, (rest.head?.map FullFof.Token.start).getD endOffset⟩
      else if !Coverage.FramerV2.objectsWellUsed value.original then .error ⟨.invalid, value.original.start⟩
      else match (Coverage.FramerV2.cutRecord pieces).2 with
        | none => .ok value
        | some annotationPieces => match Coverage.FramerV2.annotation annotationPieces with
          | .error problem => .error problem
          | .ok () => .ok value

theorem formulaRecordFast_eq (seen : List Name) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    formulaRecordFast seen endOffset pieces = formulaRecord seen endOffset pieces := by
  unfold formulaRecordFast formulaRecord
  cases Coverage.FramerV2.nameGuard pieces with
  | error problem => rfl
  | ok done =>
    simp only
    rw [Bytes.declarationC_eq rfl]
    unfold RoleByte.declaration
    cases Bytes.declaration seen endOffset
        ((Coverage.FramerV2.cutRecord pieces).1.map Coverage.FramerV2.coreToken) with
    | error problem => rfl
    | ok pair => rfl

/-- `statements` with the reversed statement splitter and the counted record decoder. -/
def statementsFast : Nat → List Name → Nat → List Coverage.FramerV2.Piece → Except Error (List RoleStatement)
  | 0, _, endOffset, _ => .error ⟨.resource, endOffset⟩
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, first :: more =>
    if seen.length ≥ 1000 then .error ⟨.resource, first.start⟩
    else
      let split := Coverage.FramerV2.splitStatementFast 0 [] (first :: more)
      match Coverage.FramerV2.keyword split.1 with
      | some "include" =>
        match Coverage.FramerV2.directive split.1 with
        | .error problem => .error problem
        | .ok (parts, selection) =>
          match statementsFast fuel seen endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecordFast seen endOffset split.1 with
        | .error problem => .error problem
        | .ok value =>
          match statementsFast fuel (value.original.name :: seen) endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.formula value :: tail)

theorem statementsFast_eq : ∀ (fuel : Nat) (seen : List Name) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece),
    statementsFast fuel seen endOffset pieces = statements fuel seen endOffset pieces
  | 0, _, _, _ => by
    unfold statementsFast statements
    rfl
  | fuel + 1, seen, endOffset, [] => by
    unfold statementsFast statements
    rfl
  | fuel + 1, seen, endOffset, first :: more => by
    unfold statementsFast statements
    simp only [Coverage.FramerV2.splitStatementFast_eq, List.reverse_nil, formulaRecordFast_eq, statementsFast_eq]
    rfl

def frameFileFast (bytes : List UInt8) (maximum : Nat) : Except Error (List RoleStatement) :=
  match fast bytes maximum with
  | .error problem => .error problem
  | .ok pieces => statementsFast (pieces.length + 1) [] bytes.length pieces

def frameBundleFast : List (Coverage.Key × List UInt8) → Nat → Except Error RoleBundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFileFast bytes maximum with
    | .error problem => .error problem
    | .ok framed => match frameBundleFast rest maximum with
      | .error problem => .error problem
      | .ok others => .ok (⟨key, framed⟩ :: others)

theorem frameFileFast_eq (bytes : List UInt8) (maximum : Nat) :
    frameFileFast bytes maximum = frameFile gated bytes maximum := by
  unfold frameFileFast frameFile
  rw [fast_eq_gated]
  cases gated bytes maximum with
  | error problem => rfl
  | ok pieces => exact statementsFast_eq _ _ _ _

/-- The fast framer is the gated revision-2 role framer. -/
theorem frameBundleFast_eq : ∀ (files : List (Coverage.Key × List UInt8)) (maximum : Nat),
    frameBundleFast files maximum = frameBundle gated files maximum
  | [], _ => rfl
  | (key, bytes) :: rest, maximum => by
    simp only [frameBundleFast, frameBundle, frameFileFast_eq, frameBundleFast_eq rest maximum]
    rfl

/-! Read, replay and version-8 acceptance over the fast framer. -/

def readBundleFast (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat) :
    Except ReadError BundleRead :=
  match frameBundleFast files maximumBytes with
  | .error problem => .error (.frame problem)
  | .ok bundle =>
    match Coverage.expand (forget bundle) bundleFuel with
    | .error problem => .error (.expand problem)
    | .ok items =>
      if Coverage.FramerV2.wellShaped (forget bundle) bundleFuel then
        if Bytes.modesValid (entriesOf bundle items) then
          match readSigned (entriesOf bundle items) with
          | none => .error .nonliteral
          | some input => .ok ⟨bundle, items, input⟩
        else .error .modes
      else .error .shape

theorem readBundleFast_eq (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat) :
    readBundleFast files maximumBytes = readBundle gated files maximumBytes := by
  unfold readBundleFast readBundle
  rw [frameBundleFast_eq]
  rfl

def prepareGoalFast (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except TaskError BundleGoalPrepared := do
  let read ← (readBundleFast files maximumBytes).mapError .read
  let some (before, goal, after) := (Signed.goalSplits read.input)[index]? | .error .noGoal
  let some (item, _) := (goalItems read.bundle read.items)[index]? | .error .noGoal
  let some task := goalTask before goal after | .error .cnfGoal
  let replay ← (Signed.replayTask read.input (task ++ distinctItems read.input read.bundle read.items)
    limits maximumPredicates maximumLiterals).mapError .replay
  pure ⟨item, replay⟩

def prepareInputsFast (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except TaskError Signed.SignedPrepared := do
  let read ← (readBundleFast files maximumBytes).mapError .read
  if (goalItems read.bundle read.items).isEmpty then
    (Signed.replayTask read.input (inputsTask read.input ++ distinctItems read.input read.bundle read.items)
      limits maximumPredicates maximumLiterals).mapError .replay
  else .error .goalsPresent

theorem prepareGoalFast_eq (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    prepareGoalFast files maximumBytes index limits maximumPredicates maximumLiterals =
      prepareGoal gated files maximumBytes index limits maximumPredicates maximumLiterals := by
  unfold prepareGoalFast prepareGoal
  rw [readBundleFast_eq]
  rfl

theorem prepareInputsFast_eq (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    prepareInputsFast files maximumBytes limits maximumPredicates maximumLiterals =
      prepareInputs gated files maximumBytes limits maximumPredicates maximumLiterals := by
  unfold prepareInputsFast prepareInputs
  rw [readBundleFast_eq]

def acceptsGoalFast (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except AcceptError Coverage.Item := do
  let prepared ← (prepareGoalFast files maximumBytes index limits maximumPredicates maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate
  pure prepared.item

def acceptsInputsFast (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except AcceptError Unit := do
  let prepared ← (prepareInputsFast files maximumBytes limits maximumPredicates maximumLiterals).mapError .task
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError
    .certificate

theorem acceptsGoalFast_eq (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsGoalFast files maximumBytes index proof limits maximumPredicates maximumLiterals =
      acceptsGoal gated files maximumBytes index proof limits maximumPredicates maximumLiterals := by
  unfold acceptsGoalFast acceptsGoal
  rw [prepareGoalFast_eq]

theorem acceptsInputsFast_eq (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsInputsFast files maximumBytes proof limits maximumPredicates maximumLiterals =
      acceptsInputs gated files maximumBytes proof limits maximumPredicates maximumLiterals := by
  unfold acceptsInputsFast acceptsInputs
  rw [prepareInputsFast_eq]

theorem acceptsGoalFast_entails {files maximumBytes index proof limits maximumPredicates maximumLiterals item}
    (accepted : acceptsGoalFast files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok item) :
    GoalEntailed gated files maximumBytes bundleFuel item := by
  rw [acceptsGoalFast_eq] at accepted
  exact acceptsGoal_entails accepted

theorem acceptsInputsFast_unsat {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsInputsFast files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ByteUnsatisfiable gated files maximumBytes bundleFuel := by
  rw [acceptsInputsFast_eq] at accepted
  exact acceptsInputs_unsat accepted

/-- Theorem endpoint over the fast framer: at least one selected conjecture, and an accepted version-8 certificate for every goal item. -/
theorem acceptsGoalsFast_theorem {files maximumBytes bundle items limits maximumPredicates maximumLiterals}
    (expanded : Expanded gated files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index proof,
      acceptsGoalFast files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok pair.1) :
    ByteTheorem gated files maximumBytes bundleFuel :=
  acceptsGoals_theorem expanded nonempty fun pair member => by
    obtain ⟨index, proof, run⟩ := accepted pair member
    exact ⟨index, proof, (acceptsGoalFast_eq files maximumBytes index proof limits maximumPredicates
      maximumLiterals) ▸ run⟩

#print axioms Fang.TptpCandidate.Roles.Bundle.V2.fast_eq_gated
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.frameBundle_fast
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.formulaRecordFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.statementsFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.frameFileFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.frameBundleFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.readBundleFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.prepareGoalFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.prepareInputsFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.acceptsGoalFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.acceptsInputsFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.acceptsGoalFast_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.acceptsInputsFast_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.acceptsGoalsFast_theorem

end Fang.TptpCandidate.Roles.Bundle.V2
