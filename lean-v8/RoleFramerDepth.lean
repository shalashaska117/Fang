/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Role bundle framing at any formula-depth and declaration-count bound.
   The hashed framer is proved equal to the list specification. -/
import RoleMeaningDepth

namespace Fang.TptpCandidate.Roles.Bundle.V3.Depth
open FullFof Numeric

def formulaRecord (maxDepth : Nat) (seen : List Name) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    Except Error Bytes.Entry :=
  match Coverage.FramerV2.nameGuard pieces with
  | .error problem => .error problem
  | .ok () =>
    match Bytes.declarationD maxDepth seen endOffset
        ((Coverage.FramerV2.cutRecord pieces).1.map Coverage.FramerV2.coreToken) with
    | .error problem => .error problem
    | .ok (value, rest) =>
      if !rest.isEmpty then .error ⟨.invalid, (rest.head?.map FullFof.Token.start).getD endOffset⟩
      else if !Coverage.FramerV2.objectsWellUsed value.original then .error ⟨.invalid, value.original.start⟩
      else match (Coverage.FramerV2.cutRecord pieces).2 with
        | none => .ok value
        | some annotationPieces => match Coverage.FramerV2.annotation annotationPieces with
          | .error problem => .error problem
          | .ok () => .ok value

theorem formulaRecord_sound {maxDepth : Nat} {seen : List Name} {endOffset : Nat} {pieces : List Coverage.FramerV2.Piece}
    {value : Bytes.Entry} (success : formulaRecord maxDepth seen endOffset pieces = .ok value) : RoleDecoded value := by
  cases guard : Coverage.FramerV2.nameGuard pieces with
  | error problem => simp [formulaRecord, guard] at success
  | ok done =>
    cases decoded : Bytes.declarationD maxDepth seen endOffset
        ((Coverage.FramerV2.cutRecord pieces).1.map Coverage.FramerV2.coreToken) with
    | error problem => simp [formulaRecord, guard, decoded] at success
    | ok pair =>
      obtain ⟨found, rest⟩ := pair
      by_cases empty : rest.isEmpty = true
      · by_cases used : Coverage.FramerV2.objectsWellUsed found.original = true
        · have same : found = value := by
            cases annotationAt : (Coverage.FramerV2.cutRecord pieces).2 with
            | none =>
              simp [formulaRecord, guard, decoded, empty, used, annotationAt] at success
              exact success
            | some annotationPieces =>
              cases annotated : Coverage.FramerV2.annotation annotationPieces with
              | error problem =>
                simp [formulaRecord, guard, decoded, empty, used, annotationAt, annotated] at success
              | ok finished =>
                simp [formulaRecord, guard, decoded, empty, used, annotationAt, annotated] at success
                exact success
          subst same
          have restNil : rest = [] := List.isEmpty_iff.mp empty
          subst restNil
          exact ⟨maxDepth, seen, endOffset, _, decoded, used⟩
        · simp [formulaRecord, guard, decoded, empty, used] at success
      · simp [formulaRecord, guard, decoded, empty] at success

def formulaRecordFast (maxDepth : Nat) (seen : List Name) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    Except Error Bytes.Entry :=
  match Coverage.FramerV2.nameGuard pieces with
  | .error problem => .error problem
  | .ok () =>
    let tokens := (Coverage.FramerV2.cutRecord pieces).1.map Coverage.FramerV2.coreToken
    match Bytes.declarationCD maxDepth seen endOffset tokens tokens.length with
    | .error problem => .error problem
    | .ok (value, rest, _) =>
      if !rest.isEmpty then .error ⟨.invalid, (rest.head?.map FullFof.Token.start).getD endOffset⟩
      else if !Coverage.FramerV2.objectsWellUsed value.original then .error ⟨.invalid, value.original.start⟩
      else match (Coverage.FramerV2.cutRecord pieces).2 with
        | none => .ok value
        | some annotationPieces => match Coverage.FramerV2.annotation annotationPieces with
          | .error problem => .error problem
          | .ok () => .ok value

theorem formulaRecordFast_eq (maxDepth : Nat) (seen : List Name) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    formulaRecordFast maxDepth seen endOffset pieces = formulaRecord maxDepth seen endOffset pieces := by
  unfold formulaRecordFast formulaRecord
  cases Coverage.FramerV2.nameGuard pieces with
  | error problem => rfl
  | ok done =>
    simp only
    rw [Bytes.declarationCD_eq rfl]
    cases Bytes.declarationD maxDepth seen endOffset
        ((Coverage.FramerV2.cutRecord pieces).1.map Coverage.FramerV2.coreToken) with
    | error problem => rfl
    | ok pair => rfl

def statements (limit maxDepth : Nat) : Nat → List Name → Nat → List Coverage.FramerV2.Piece → Except Error (List RoleStatement)
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
          match statements limit maxDepth fuel seen endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecord maxDepth seen endOffset split.1 with
        | .error problem => .error problem
        | .ok value =>
          match statements limit maxDepth fuel (value.original.name :: seen) endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.formula value :: tail)

def frameFile (limit maxDepth : Nat) (tokenize : V2.Tokenizer) (bytes : List UInt8) (maximum : Nat) :
    Except Error (List RoleStatement) :=
  match tokenize bytes maximum with
  | .error problem => .error problem
  | .ok pieces => statements limit maxDepth (pieces.length + 1) [] bytes.length pieces

def frameBundle (limit maxDepth : Nat) (tokenize : V2.Tokenizer) : List (Coverage.Key × List UInt8) → Nat → Except Error RoleBundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFile limit maxDepth tokenize bytes maximum with
    | .error problem => .error problem
    | .ok framed => match frameBundle limit maxDepth tokenize rest maximum with
      | .error problem => .error problem
      | .ok others => .ok (⟨key, framed⟩ :: others)

/-- Every framed record has a decoder witness at the chosen depth. -/
theorem statements_sound (limit maxDepth : Nat) : ∀ fuel seen endOffset pieces result,
    statements limit maxDepth fuel seen endOffset pieces = .ok result →
      ∀ value, RoleStatement.formula value ∈ result → RoleDecoded value := by
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
                exact formulaRecord_sound recorded
              · exact ih _ _ _ _ later value inTail

theorem frameBundle_sound (limit maxDepth : Nat) (tokenize : V2.Tokenizer) : FrameSound (frameBundle limit maxDepth tokenize) := by
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
          · exact statements_sound limit maxDepth _ _ _ _ _ framedAt value present
        · exact ih tail file later value present

/-! The hashed framer. -/

/-- `formulaRecordFast` with the duplicate test as a parameter. -/
def formulaRecordHashed (maxDepth : Nat) (isSeen : Name → Bool) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    Except Error Bytes.Entry :=
  match Coverage.FramerV2.nameGuard pieces with
  | .error problem => .error problem
  | .ok () =>
    let tokens := (Coverage.FramerV2.cutRecord pieces).1.map Coverage.FramerV2.coreToken
    match Bytes.declarationSeenCD maxDepth isSeen endOffset tokens tokens.length with
    | .error problem => .error problem
    | .ok (value, rest, _) =>
      if !rest.isEmpty then .error ⟨.invalid, (rest.head?.map FullFof.Token.start).getD endOffset⟩
      else if !Coverage.FramerV2.objectsWellUsed value.original then .error ⟨.invalid, value.original.start⟩
      else match (Coverage.FramerV2.cutRecord pieces).2 with
        | none => .ok value
        | some annotationPieces => match Coverage.FramerV2.annotation annotationPieces with
          | .error problem => .error problem
          | .ok () => .ok value

theorem formulaRecordHashed_eq {maxDepth : Nat} {isSeen : Name → Bool} {seen : List Name} (same : ∀ label, isSeen label = seen.contains label)
    (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    formulaRecordHashed maxDepth isSeen endOffset pieces = formulaRecord maxDepth seen endOffset pieces := by
  rw [← formulaRecordFast_eq]
  unfold formulaRecordHashed formulaRecordFast
  simp only [Bytes.declarationSeenCD_eq same]

def statementsHashed (limit maxDepth : Nat) : Nat → Std.HashSet Name → Nat → Nat → List Coverage.FramerV2.Piece →
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
          match statementsHashed limit maxDepth fuel seen seenCount endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecordHashed maxDepth (fun label => seen.contains label) endOffset split.1 with
        | .error problem => .error problem
        | .ok value =>
          match statementsHashed limit maxDepth fuel (seen.insert value.original.name) (seenCount + 1) endOffset split.2 with
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

theorem statementsHashed_eq (limit maxDepth : Nat) : ∀ fuel (set : Std.HashSet Name) seen seenCount endOffset pieces,
    (∀ label, set.contains label = seen.contains label) → seenCount = seen.length →
    statementsHashed limit maxDepth fuel set seenCount endOffset pieces = statements limit maxDepth fuel seen endOffset pieces
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
      statementsHashed_eq limit maxDepth fuel set seen seen.length endOffset _ members rfl]
    split
    · rfl
    · split
      · rfl
      · rfl
      · cases formulaRecord maxDepth seen endOffset (Coverage.FramerV2.splitStatement 0 [] (first :: more)).1 with
        | error problem => rfl
        | ok value =>
          simp only
          rw [statementsHashed_eq limit maxDepth fuel (set.insert value.original.name) (value.original.name :: seen)
            (seen.length + 1) endOffset _ (contains_insert_cons members value.original.name) (by simp)]

def frameFileHashed (limit maxDepth : Nat) (bytes : List UInt8) (maximum : Nat) : Except Error (List RoleStatement) :=
  match V2.fast bytes maximum with
  | .error problem => .error problem
  | .ok pieces => statementsHashed limit maxDepth (pieces.length + 1) {} 0 bytes.length pieces

def frameBundleHashed (limit maxDepth : Nat) : List (Coverage.Key × List UInt8) → Nat → Except Error RoleBundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFileHashed limit maxDepth bytes maximum with
    | .error problem => .error problem
    | .ok framed => match frameBundleHashed limit maxDepth rest maximum with
      | .error problem => .error problem
      | .ok others => .ok (⟨key, framed⟩ :: others)

theorem frameFileHashed_eq (limit maxDepth : Nat) (bytes : List UInt8) (maximum : Nat) :
    frameFileHashed limit maxDepth bytes maximum = frameFile limit maxDepth V2.gated bytes maximum := by
  unfold frameFileHashed frameFile
  rw [V2.fast_eq_gated]
  cases V2.gated bytes maximum with
  | error problem => rfl
  | ok pieces => exact statementsHashed_eq limit maxDepth _ {} [] 0 _ _ (by intro label; simp) rfl

/-- The hashed framer is the list framer with the same limit and the gated tokenizer. -/
theorem frameBundleHashed_eq (limit maxDepth : Nat) : frameBundleHashed limit maxDepth = frameBundle limit maxDepth V2.gated := by
  funext files maximum
  induction files with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨key, bytes⟩ := first
    simp only [frameBundleHashed, frameBundle, frameFileHashed_eq, ih]

theorem frameBundleHashed_sound (limit maxDepth : Nat) : FrameSound (frameBundleHashed limit maxDepth) := by
  rw [frameBundleHashed_eq]
  exact frameBundle_sound limit maxDepth V2.gated


theorem formulaRecord_accepted : formulaRecord 64 = V2.formulaRecord := by
  funext seen endOffset pieces
  unfold formulaRecord V2.formulaRecord RoleByte.declaration
  rw [Bytes.declarationD_accepted]
  rfl

theorem statements_accepted (limit : Nat) : ∀ fuel seen endOffset pieces,
    statements limit 64 fuel seen endOffset pieces = V3.statements limit fuel seen endOffset pieces
  | 0, _, _, _ => rfl
  | _ + 1, _, _, [] => rfl
  | fuel + 1, seen, endOffset, first :: more => by
    unfold statements V3.statements
    simp only [formulaRecord_accepted, statements_accepted limit fuel]
    rfl

theorem frameBundle_accepted (limit : Nat) (tokenize : V2.Tokenizer) :
    frameBundle limit 64 tokenize = V3.frameBundle limit tokenize := by
  funext files maximum
  induction files with
  | nil => rfl
  | cons first rest ih =>
    obtain ⟨key, bytes⟩ := first
    simp only [frameBundle, V3.frameBundle, frameFile, V3.frameFile, statements_accepted, ih]
    rfl

theorem frameBundleHashed_accepted (limit : Nat) : frameBundleHashed limit 64 = V3.frameBundleHashed limit := by
  rw [frameBundleHashed_eq, V3.frameBundleHashed_eq, frameBundle_accepted]

end Fang.TptpCandidate.Roles.Bundle.V3.Depth
