/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The hashed bundle framer of the limits record: the linear lexer `tokenizeFast`, the reversed statement splitter `splitStatementFast`, and records read by the counted decoder `declarationSeenC` with a `Std.HashSet Name` of seen names (their `Hashable Name` instance) and a count of them. `frameBundleHashed_eq` proves it equal to the list framer `FramerLimit.frameBundle` with the same limit, so it is a sound frame and at 1,000 it is framer revision 2. The pattern is the role framer's `RoleFramerLimit`. -/
import BundleFramerLimit
import BundleFastLexer
import ExpandedLimitDecoder

namespace Fang.TptpCandidate.FullFof.Coverage.FramerLimit

open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2 (Piece splitStatement splitStatementFast splitStatementFast_eq
  keyword directive formulaRecord nameGuard cutRecord coreToken objectsWellUsed annotation tokenizeFast tokenizeFast_eq)

/-- `FramerV2.formulaRecord` with the duplicate test as a parameter and the counted record decoder. -/
def formulaRecordHashed (isSeen : Name → Bool) (endOffset : Nat) (pieces : List Piece) :
    Except Error Declaration :=
  match nameGuard pieces with
  | .error failure => .error failure
  | .ok () =>
    let tokens := (cutRecord pieces).1.map coreToken
    match Integration.declarationSeenC isSeen endOffset tokens tokens.length with
    | .error failure => .error failure
    | .ok (value, rest, _) =>
      if !rest.isEmpty then .error ⟨.invalid, (rest.head?.map Token.start).getD endOffset⟩
      else if !objectsWellUsed value then .error ⟨.invalid, value.start⟩
      else match (cutRecord pieces).2 with
        | none => .ok value
        | some annotationPieces => match annotation annotationPieces with
          | .error failure => .error failure
          | .ok () => .ok value

theorem formulaRecordHashed_eq {isSeen : Name → Bool} {seen : List Name}
    (same : ∀ label, isSeen label = seen.contains label) (endOffset : Nat) (pieces : List Piece) :
    formulaRecordHashed isSeen endOffset pieces = formulaRecord seen endOffset pieces := by
  unfold formulaRecordHashed formulaRecord
  simp only [Integration.declarationSeenC_eq same, Integration.declarationC_eq rfl]
  cases nameGuard pieces with
  | error failure => rfl
  | ok done =>
    cases CnfBoolean.declaration seen endOffset ((cutRecord pieces).1.map coreToken) with
    | error failure => rfl
    | ok pair => rfl

def statementsHashed (limit : Nat) : Nat → Std.HashSet Name → Nat → Nat → List Piece →
    Except Error (List Statement)
  | 0, _, _, endOffset, _ => .error ⟨.resource, endOffset⟩
  | _ + 1, _, _, _, [] => .ok []
  | fuel + 1, seen, seenCount, endOffset, first :: more =>
    if seenCount ≥ limit then .error ⟨.resource, first.start⟩
    else
      let split := splitStatementFast 0 [] (first :: more)
      match keyword split.1 with
      | some "include" =>
        match directive split.1 with
        | .error failure => .error failure
        | .ok (parts, selection) =>
          match statementsHashed limit fuel seen seenCount endOffset split.2 with
          | .error failure => .error failure
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecordHashed (fun label => seen.contains label) endOffset split.1 with
        | .error failure => .error failure
        | .ok value =>
          match statementsHashed limit fuel (seen.insert value.name) (seenCount + 1) endOffset split.2 with
          | .error failure => .error failure
          | .ok tail => .ok (.formula value :: tail)

theorem contains_insert_cons {set : Std.HashSet Name} {seen : List Name}
    (members : ∀ label, set.contains label = seen.contains label) (added : Name) :
    ∀ label, (set.insert added).contains label = (added :: seen).contains label := by
  intro label
  rw [Std.HashSet.contains_insert, members, List.contains_cons]
  by_cases same : label = added
  · subst same
    simp
  · have other : added ≠ label := fun reversed => same reversed.symm
    rw [beq_false_of_ne other, beq_false_of_ne same]

theorem statementsHashed_eq (limit : Nat) : ∀ fuel (set : Std.HashSet Name) seen seenCount endOffset pieces,
    (∀ label, set.contains label = seen.contains label) → seenCount = seen.length →
    statementsHashed limit fuel set seenCount endOffset pieces = statements limit fuel seen endOffset pieces
  | 0, _, _, _, _, _, _, _ => by
    unfold statementsHashed statements
    rfl
  | _ + 1, _, _, _, _, [], _, _ => by
    unfold statementsHashed statements
    rfl
  | fuel + 1, set, seen, seenCount, endOffset, first :: more, members, counted => by
    subst counted
    have step : ∀ (added : Name) (pieces : List Piece),
        statementsHashed limit fuel (set.insert added) (seen.length + 1) endOffset pieces =
          statements limit fuel (added :: seen) endOffset pieces := fun added pieces =>
      statementsHashed_eq limit fuel (set.insert added) (added :: seen) (seen.length + 1) endOffset pieces
        (contains_insert_cons members added) (by simp)
    unfold statementsHashed statements
    simp only [splitStatementFast_eq, List.reverse_nil, formulaRecordHashed_eq members, step,
      statementsHashed_eq limit fuel set seen seen.length endOffset _ members rfl]
    -- The two definitions use distinct auxiliary match functions with equal bodies.
    rfl

def frameFileHashed (limit : Nat) (bytes : List UInt8) (maximum : Nat) : Except Error (List Statement) :=
  match tokenizeFast bytes maximum with
  | .error failure => .error failure
  | .ok pieces => statementsHashed limit (pieces.length + 1) {} 0 bytes.length pieces

def frameBundleHashed (limit : Nat) : List (Key × List UInt8) → Nat → Except Error Bundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFileHashed limit bytes maximum with
    | .error failure => .error failure
    | .ok framed => match frameBundleHashed limit rest maximum with
      | .error failure => .error failure
      | .ok others => .ok (⟨key, framed⟩ :: others)

theorem frameFileHashed_eq (limit : Nat) (bytes : List UInt8) (maximum : Nat) :
    frameFileHashed limit bytes maximum = frameFile limit bytes maximum := by
  unfold frameFileHashed frameFile
  rw [tokenizeFast_eq]
  cases FramerV2.tokenize bytes maximum with
  | error failure => rfl
  | ok pieces => exact statementsHashed_eq limit _ {} [] 0 _ _ (by intro label; simp) rfl

/-- The hashed framer is the list framer with the same limit. -/
theorem frameBundleHashed_eq (limit : Nat) : frameBundleHashed limit = frameBundle limit := by
  funext files maximum
  induction files with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨key, bytes⟩ := first
    simp only [frameBundleHashed, frameBundle, frameFileHashed_eq, ih]
    rfl

theorem frameBundleHashed_sound (limit : Nat) : FrameSound (frameBundleHashed limit) := by
  rw [frameBundleHashed_eq]
  exact frameBundle_sound limit

/-- At 1,000 formulas per file the hashed framer is framer revision 2. -/
theorem frameBundleHashed_accepted : frameBundleHashed 1000 = FramerV2.frameBundle := by
  rw [frameBundleHashed_eq]
  funext files maximum
  exact frameBundle_accepted files maximum

#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.formulaRecordHashed_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.contains_insert_cons
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.statementsHashed_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.frameFileHashed_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.frameBundleHashed_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.frameBundleHashed_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.frameBundleHashed_accepted

end Fang.TptpCandidate.FullFof.Coverage.FramerLimit
