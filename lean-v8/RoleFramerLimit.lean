/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The revision-2 role framer with the per-file declaration limit as a parameter. The list framer with limit 1,000 is the revision-2 role framer. The hashed framer uses the linear lexer, the reversed statement splitter, the counted record decoder with a hash set of seen names and a declaration counter, and is proved equal to the list framer with the same limit. Soundness is stated for any frame function, so the meanings and entries in `RoleMeaningLimit` and `RoleReplayLimit` take the frame as a parameter. -/
import RoleFramerFast
import RoleDecoderLimit

namespace Fang.TptpCandidate.Roles.Bundle.V3
open FullFof Numeric

/-- Every formula statement of the bundle is a role-decoder record. -/
def SoundBundle (bundle : RoleBundle) : Prop :=
  ∀ file ∈ bundle, ∀ value, RoleStatement.formula value ∈ file.statements → V2.RoleDecoded value

/-- A frame function whose every result is a sound bundle. -/
def FrameSound (frame : List (Coverage.Key × List UInt8) → Nat → Except Error RoleBundle) : Prop :=
  ∀ {files maximum bundle}, frame files maximum = .ok bundle → SoundBundle bundle

/-! The list framer with the limit as a parameter. -/

/-- `V2.statements` with `limit` in place of 1,000. -/
def statements (limit : Nat) : Nat → List Name → Nat → List Coverage.FramerV2.Piece → Except Error (List RoleStatement)
  | 0, _, endOffset, _ => .error ⟨.resource, endOffset⟩
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, first :: more =>
    if seen.length ≥ limit then .error ⟨.resource, first.start⟩
    else
      let split := Coverage.FramerV2.splitStatement 0 [] (first :: more)
      match Coverage.FramerV2.keyword split.1 with
      | some "include" =>
        match Coverage.FramerV2.directive split.1 with
        | .error problem => .error problem
        | .ok (parts, selection) =>
          match statements limit fuel seen endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match V2.formulaRecord seen endOffset split.1 with
        | .error problem => .error problem
        | .ok value =>
          match statements limit fuel (value.original.name :: seen) endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.formula value :: tail)

theorem statements_accepted : ∀ (fuel : Nat) (seen : List Name) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece),
    statements 1000 fuel seen endOffset pieces = V2.statements fuel seen endOffset pieces
  | 0, _, _, _ => by
    unfold statements V2.statements
    rfl
  | fuel + 1, seen, endOffset, [] => by
    unfold statements V2.statements
    rfl
  | fuel + 1, seen, endOffset, first :: more => by
    unfold statements V2.statements
    simp only [statements_accepted]
    rfl

def frameFile (limit : Nat) (tokenize : V2.Tokenizer) (bytes : List UInt8) (maximum : Nat) :
    Except Error (List RoleStatement) :=
  match tokenize bytes maximum with
  | .error problem => .error problem
  | .ok pieces => statements limit (pieces.length + 1) [] bytes.length pieces

def frameBundle (limit : Nat) (tokenize : V2.Tokenizer) : List (Coverage.Key × List UInt8) → Nat → Except Error RoleBundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFile limit tokenize bytes maximum with
    | .error problem => .error problem
    | .ok framed => match frameBundle limit tokenize rest maximum with
      | .error problem => .error problem
      | .ok others => .ok (⟨key, framed⟩ :: others)

/-- With limit 1,000 the list framer is the revision-2 role framer. -/
theorem frameBundle_accepted (tokenize : V2.Tokenizer) : ∀ (files : List (Coverage.Key × List UInt8)) (maximum : Nat),
    frameBundle 1000 tokenize files maximum = V2.frameBundle tokenize files maximum
  | [], _ => rfl
  | (key, bytes) :: rest, maximum => by
    simp only [frameBundle, V2.frameBundle, frameFile, V2.frameFile, statements_accepted,
      frameBundle_accepted tokenize rest maximum]
    rfl

theorem statements_sound (limit : Nat) : ∀ fuel seen endOffset pieces result,
    statements limit fuel seen endOffset pieces = .ok result →
      ∀ value, RoleStatement.formula value ∈ result → V2.RoleDecoded value := by
  intro fuel
  induction fuel with
  | zero => intro seen endOffset pieces result success; simp [statements] at success
  | succ fuel ih =>
    intro seen endOffset pieces result success value member
    cases pieces with
    | nil =>
      simp only [statements, Except.ok.injEq] at success
      subst success
      simp at member
    | cons first more =>
      simp only [statements] at success
      split at success
      · cases success
      · split at success
        · split at success
          · cases success
          · split at success
            · cases success
            · rename_i tail later
              simp only [Except.ok.injEq] at success
              subst success
              rcases List.mem_cons.mp member with same | inTail
              · cases same
              · exact ih _ _ _ _ later value inTail
        · cases success
        · split at success
          · cases success
          · rename_i found recorded
            split at success
            · cases success
            · rename_i tail later
              simp only [Except.ok.injEq] at success
              subst success
              rcases List.mem_cons.mp member with same | inTail
              · cases same
                exact V2.formulaRecord_sound recorded
              · exact ih _ _ _ _ later value inTail

theorem frameBundle_sound (limit : Nat) (tokenize : V2.Tokenizer) : FrameSound (frameBundle limit tokenize) := by
  intro files maximum bundle success
  induction files generalizing bundle with
  | nil => simp only [frameBundle, Except.ok.injEq] at success; subst success; simp [SoundBundle]
  | cons first rest ih =>
    obtain ⟨key, bytes⟩ := first
    simp only [frameBundle] at success
    split at success
    · cases success
    · rename_i framed framedAt
      split at success
      · cases success
      · rename_i others tail
        simp only [Except.ok.injEq] at success
        subst success
        intro file member value present
        rcases List.mem_cons.mp member with same | later
        · subst same
          unfold frameFile at framedAt
          split at framedAt
          · cases framedAt
          · exact statements_sound limit _ _ _ _ _ framedAt value present
        · exact ih tail file later value present

/-! The hashed framer. -/

/-- `V2.formulaRecordFast` with the duplicate test as a parameter. -/
def formulaRecordHashed (isSeen : Name → Bool) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    Except Error Bytes.Entry :=
  match Coverage.FramerV2.nameGuard pieces with
  | .error problem => .error problem
  | .ok () =>
    let tokens := (Coverage.FramerV2.cutRecord pieces).1.map Coverage.FramerV2.coreToken
    match Bytes.declarationSeenC isSeen endOffset tokens tokens.length with
    | .error problem => .error problem
    | .ok (value, rest, _) =>
      if !rest.isEmpty then .error ⟨.invalid, (rest.head?.map FullFof.Token.start).getD endOffset⟩
      else if !Coverage.FramerV2.objectsWellUsed value.original then .error ⟨.invalid, value.original.start⟩
      else match (Coverage.FramerV2.cutRecord pieces).2 with
        | none => .ok value
        | some annotationPieces => match Coverage.FramerV2.annotation annotationPieces with
          | .error problem => .error problem
          | .ok () => .ok value

theorem formulaRecordHashed_eq {isSeen : Name → Bool} {seen : List Name} (same : ∀ label, isSeen label = seen.contains label)
    (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    formulaRecordHashed isSeen endOffset pieces = V2.formulaRecord seen endOffset pieces := by
  rw [← V2.formulaRecordFast_eq]
  unfold formulaRecordHashed V2.formulaRecordFast
  simp only [Bytes.declarationSeenC_eq same]
  rfl

def statementsHashed (limit : Nat) : Nat → Std.HashSet Name → Nat → Nat → List Coverage.FramerV2.Piece →
    Except Error (List RoleStatement)
  | 0, _, _, endOffset, _ => .error ⟨.resource, endOffset⟩
  | _ + 1, _, _, _, [] => .ok []
  | fuel + 1, seen, seenCount, endOffset, first :: more =>
    if seenCount ≥ limit then .error ⟨.resource, first.start⟩
    else
      let split := Coverage.FramerV2.splitStatementFast 0 [] (first :: more)
      match Coverage.FramerV2.keyword split.1 with
      | some "include" =>
        match Coverage.FramerV2.directive split.1 with
        | .error problem => .error problem
        | .ok (parts, selection) =>
          match statementsHashed limit fuel seen seenCount endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecordHashed (fun label => seen.contains label) endOffset split.1 with
        | .error problem => .error problem
        | .ok value =>
          match statementsHashed limit fuel (seen.insert value.original.name) (seenCount + 1) endOffset split.2 with
          | .error problem => .error problem
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
    unfold statementsHashed statements
    simp only [Coverage.FramerV2.splitStatementFast_eq, List.reverse_nil, formulaRecordHashed_eq members,
      statementsHashed_eq limit fuel set seen seen.length endOffset _ members rfl]
    split
    · rfl
    · split
      · rfl
      · rfl
      · cases V2.formulaRecord seen endOffset (Coverage.FramerV2.splitStatement 0 [] (first :: more)).1 with
        | error problem => rfl
        | ok value =>
          simp only
          rw [statementsHashed_eq limit fuel (set.insert value.original.name) (value.original.name :: seen)
            (seen.length + 1) endOffset _ (contains_insert_cons members value.original.name) (by simp)]

def frameFileHashed (limit : Nat) (bytes : List UInt8) (maximum : Nat) : Except Error (List RoleStatement) :=
  match V2.fast bytes maximum with
  | .error problem => .error problem
  | .ok pieces => statementsHashed limit (pieces.length + 1) {} 0 bytes.length pieces

def frameBundleHashed (limit : Nat) : List (Coverage.Key × List UInt8) → Nat → Except Error RoleBundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFileHashed limit bytes maximum with
    | .error problem => .error problem
    | .ok framed => match frameBundleHashed limit rest maximum with
      | .error problem => .error problem
      | .ok others => .ok (⟨key, framed⟩ :: others)

theorem frameFileHashed_eq (limit : Nat) (bytes : List UInt8) (maximum : Nat) :
    frameFileHashed limit bytes maximum = frameFile limit V2.gated bytes maximum := by
  unfold frameFileHashed frameFile
  rw [V2.fast_eq_gated]
  cases V2.gated bytes maximum with
  | error problem => rfl
  | ok pieces => exact statementsHashed_eq limit _ {} [] 0 _ _ (by intro label; simp) rfl

/-- The hashed framer is the list framer with the same limit and the gated tokenizer. -/
theorem frameBundleHashed_eq (limit : Nat) : frameBundleHashed limit = frameBundle limit V2.gated := by
  funext files maximum
  induction files with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨key, bytes⟩ := first
    simp only [frameBundleHashed, frameBundle, frameFileHashed_eq, ih]

theorem frameBundleHashed_sound (limit : Nat) : FrameSound (frameBundleHashed limit) := by
  rw [frameBundleHashed_eq]
  exact frameBundle_sound limit V2.gated

#print axioms Fang.TptpCandidate.Roles.Bundle.V3.statements_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.frameBundle_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.statements_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.frameBundle_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.formulaRecordHashed_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.contains_insert_cons
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.statementsHashed_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.frameFileHashed_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.frameBundleHashed_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.frameBundleHashed_sound

end Fang.TptpCandidate.Roles.Bundle.V3
