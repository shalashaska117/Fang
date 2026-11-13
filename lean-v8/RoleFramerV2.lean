/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The role-aware framer over framer revision 2 (`Coverage.FramerV2`, whose `cutRecord` checks the record closing). The tokenizer is a parameter, so a faster tokenizer proved equal to the gated one gives the same framer. -/
import BundleItems
import BundleFramerSound

namespace Fang.TptpCandidate.Roles.Bundle.V2
open FullFof Numeric

/-! The role-aware framer. Every step except the tokenizer and the record decoder is a revision-2 definition. -/

/-- A tokenizer with the revision-2 piece type. -/
abbrev Tokenizer := List UInt8 → Nat → Except Error (List Coverage.FramerV2.Piece)

/-- The gated revision-2 tokenizer. -/
def gated : Tokenizer := Coverage.FramerV2.tokenize

/-- `FramerV2.formulaRecord` with `RoleByte.declaration` in place of `CnfBoolean.declaration`. -/
def formulaRecord (seen : List Name) (endOffset : Nat) (pieces : List Coverage.FramerV2.Piece) :
    Except Error Bytes.Entry :=
  match Coverage.FramerV2.nameGuard pieces with
  | .error problem => .error problem
  | .ok () =>
    match RoleByte.declaration seen endOffset
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

/-- `FramerV2.statements` over role statements. -/
def statements : Nat → List Name → Nat → List Coverage.FramerV2.Piece → Except Error (List RoleStatement)
  | 0, _, endOffset, _ => .error ⟨.resource, endOffset⟩
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, first :: more =>
    if seen.length ≥ 1000 then .error ⟨.resource, first.start⟩
    else
      let split := Coverage.FramerV2.splitStatement 0 [] (first :: more)
      match Coverage.FramerV2.keyword split.1 with
      | some "include" =>
        match Coverage.FramerV2.directive split.1 with
        | .error problem => .error problem
        | .ok (parts, selection) =>
          match statements fuel seen endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecord seen endOffset split.1 with
        | .error problem => .error problem
        | .ok value =>
          match statements fuel (value.original.name :: seen) endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.formula value :: tail)

def frameFile (tokenize : Tokenizer) (bytes : List UInt8) (maximum : Nat) : Except Error (List RoleStatement) :=
  match tokenize bytes maximum with
  | .error problem => .error problem
  | .ok pieces => statements (pieces.length + 1) [] bytes.length pieces

def frameBundle (tokenize : Tokenizer) : List (Coverage.Key × List UInt8) → Nat → Except Error RoleBundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFile tokenize bytes maximum with
    | .error problem => .error problem
    | .ok framed => match frameBundle tokenize rest maximum with
      | .error problem => .error problem
      | .ok others => .ok (⟨key, framed⟩ :: others)

/-- A tokenizer that agrees with another on every input gives the same framer; this is how a faster tokenizer replaces `gated`. -/
theorem frameBundle_congr {first second : Tokenizer}
    (same : ∀ bytes maximum, first bytes maximum = second bytes maximum) : frameBundle first = frameBundle second := by
  have equal : first = second := funext fun bytes => funext fun maximum => same bytes maximum
  rw [equal]

/-! Soundness: every framed formula statement is a role-decoder record, whatever the tokenizer. -/

def RoleDecoded (value : Bytes.Entry) : Prop :=
  ∃ seen endOffset tokens, RoleByte.declaration seen endOffset tokens = .ok (value, []) ∧
    Coverage.FramerV2.objectsWellUsed value.original = true

theorem formulaRecord_sound {seen : List Name} {endOffset : Nat} {pieces : List Coverage.FramerV2.Piece}
    {value : Bytes.Entry} (success : formulaRecord seen endOffset pieces = .ok value) : RoleDecoded value := by
  cases guard : Coverage.FramerV2.nameGuard pieces with
  | error problem => simp [formulaRecord, guard] at success
  | ok done =>
    cases decoded : RoleByte.declaration seen endOffset
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
          exact ⟨seen, endOffset, _, decoded, used⟩
        · simp [formulaRecord, guard, decoded, empty, used] at success
      · simp [formulaRecord, guard, decoded, empty] at success

theorem statements_sound : ∀ fuel seen endOffset pieces result,
    statements fuel seen endOffset pieces = .ok result →
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

theorem frameFile_sound {tokenize : Tokenizer} {bytes : List UInt8} {maximum : Nat} {result : List RoleStatement}
    (success : frameFile tokenize bytes maximum = .ok result) {value : Bytes.Entry}
    (member : RoleStatement.formula value ∈ result) : RoleDecoded value := by
  unfold frameFile at success
  split at success
  · cases success
  · exact statements_sound _ _ _ _ _ success value member

theorem frameBundle_sound {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (success : frameBundle tokenize files maximum = .ok bundle) :
    ∀ file ∈ bundle, ∀ value, RoleStatement.formula value ∈ file.statements → RoleDecoded value := by
  induction files generalizing bundle with
  | nil => simp only [frameBundle, Except.ok.injEq] at success; subst success; simp
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
          exact frameFile_sound framedAt present
        · exact ih tail file later value present

/-! Expanded entries. -/

theorem framed_entries_sound {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle tokenize files maximum = .ok bundle) (items : List Coverage.Item)
    {value : Bytes.Entry} (member : value ∈ entriesOf bundle items) : RoleDecoded value := by
  simp only [entriesOf, List.mem_filterMap] at member
  obtain ⟨item, _, found⟩ := member
  cases statementAt : roleStatementAt bundle item with
  | none => simp [statementAt] at found
  | some statement =>
    cases statement with
    | directive parts selection => simp [statementAt] at found
    | formula decoded =>
      simp only [statementAt, Option.some.injEq] at found
      subst found
      simp only [roleStatementAt, bind, Option.bind] at statementAt
      cases fileAt : bundle[item.1]? with
      | none => simp [fileAt] at statementAt
      | some file =>
        simp only [fileAt] at statementAt
        exact frameBundle_sound framed file (List.mem_of_getElem? fileAt) decoded
          (List.mem_of_getElem? statementAt)

theorem framed_closed {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle tokenize files maximum = .ok bundle) (items : List Coverage.Item) :
    Bytes.Closed (entriesOf bundle items) := by
  intro value member
  obtain ⟨seen, endOffset, tokens, decoded, _⟩ := framed_entries_sound framed items member
  exact Bytes.declaration_closed decoded

theorem framed_goals_fof {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle tokenize files maximum = .ok bundle) (items : List Coverage.Item)
    {value : Bytes.Entry} (member : value ∈ entriesOf bundle items) (goal : value.role = .conjecture) :
    ∃ formula, value.original.body = .fof formula := by
  obtain ⟨seen, endOffset, tokens, decoded, _⟩ := framed_entries_sound framed items member
  exact RoleByte.declaration_goal_fof decoded goal

/-! Distinct objects, with the revision-2 object names and separation. -/

def objectsOf (bundle : RoleBundle) (items : List Coverage.Item) : List String :=
  Coverage.FramerV2.objectNames (Coverage.declarationsOf (forget bundle) items)

def objectIds (input : SignedInput) (bundle : RoleBundle) (items : List Coverage.Item) : List Nat :=
  (objectsOf bundle items).map fun label => Arity.id input.functions (label, 0)

/-- The generated disequalities as positive task items. -/
def distinctItems (input : SignedInput) (bundle : RoleBundle) (items : List Coverage.Item) : List SignedNumeric :=
  (Coverage.distinctAxioms input.predicates.length (objectIds input bundle items)).map positive

theorem framed_objects_covered {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle tokenize files maximum = .ok bundle) (items : List Coverage.Item)
    {input : Integration.NumericInput}
    (encoded : Integration.readInput (Coverage.declarationsOf (forget bundle) items) = some input) :
    ∀ label ∈ objectsOf bundle items, (label, 0) ∈ input.functions := by
  intro label member
  rw [(Integration.readInput_tables encoded).1]
  simp only [objectsOf, Coverage.FramerV2.objectNames, List.mem_eraseDups, List.mem_filterMap,
    List.mem_flatMap] at member
  obtain ⟨symbol, ⟨formula, formulaMember, present⟩, chosen⟩ := member
  by_cases object : Coverage.FramerV2.isObject symbol.1 = true
  · simp only [object, ↓reduceIte, Option.some.injEq] at chosen
    subst chosen
    simp only [source, List.mem_map, Function.comp] at formulaMember
    obtain ⟨value, valueMember, rfl⟩ := formulaMember
    have entryMember : value ∈ (entriesOf bundle items).map Bytes.Entry.original := by
      rw [entriesOf_original]; exact valueMember
    obtain ⟨entry, entryAt, rfl⟩ := List.mem_map.mp entryMember
    obtain ⟨_, _, _, _, used⟩ := framed_entries_sound framed items entryAt
    have arity : symbol.2 = 0 := by
      simp only [Coverage.FramerV2.objectsWellUsed, Bool.and_eq_true, Bool.not_eq_true',
        List.any_eq_false] at used
      have := used.2 symbol present
      simp only [object, bne_iff_ne, ne_eq] at this
      exact Classical.byContradiction fun different => this ⟨trivial, different⟩
    have inSource : entry.original.body.formula ∈ source (Coverage.declarationsOf (forget bundle) items) :=
      List.mem_map.mpr ⟨entry.original, valueMember, rfl⟩
    have covered := (collected_covered inSource).functions symbol present
    have shape : symbol = (symbol.1, 0) := Prod.ext rfl arity
    rw [← shape]
    exact covered
  · simp [object] at chosen

theorem objectsOf_nodup (bundle : RoleBundle) (items : List Coverage.Item) : (objectsOf bundle items).Nodup := by
  unfold objectsOf Coverage.FramerV2.objectNames List.eraseDups List.eraseDupsBy
  exact eraseDups_loop_nodup _ [] List.nodup_nil

theorem objectIds_nodup {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle tokenize files maximum = .ok bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input) :
    (objectIds input bundle items).Nodup := by
  have covered := framed_objects_covered framed items (read_tables read)
  apply List.pairwise_map.mpr
  refine (objectsOf_nodup bundle items).imp_of_mem ?_
  intro first second firstMember secondMember different same
  exact different (Prod.mk.inj (Arity.id_injective (covered first firstMember)
    (covered second secondMember) same)).1

theorem distinctItems_models {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle tokenize files maximum = .ok bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input)
    {D : Type} [Nonempty D] (model : Source.Interpretation D)
    (separated : Coverage.FramerV2.NamedSeparated model (objectsOf bundle items)) :
    TaskModels (FullFof.toNumeric model input.functions input.predicates) (distinctItems input bundle items) := by
  have covered := framed_objects_covered framed items (read_tables read)
  have agreement := model_toNumeric model input.functions input.predicates
  have numeric := (Coverage.FramerV2.separated_iff agreement covered).mp separated
  have nodup := objectIds_nodup framed read
  intro item member
  obtain ⟨declaration, present, rfl⟩ := List.mem_map.mp member
  rw [positive_holds]
  obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp present
  obtain ⟨left, right⟩ := pair
  obtain ⟨leftMember, rightMember, different⟩ := Coverage.pairs_mem pairMember
  apply (Coverage.disequality_models (Arity.toNumeric model input.functions input.predicates)
    input.predicates.length left right).mpr
  exact numeric left leftMember right rightMember (different nodup)

#print axioms Fang.TptpCandidate.Roles.Bundle.V2.frameBundle_congr
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.formulaRecord_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.statements_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.frameFile_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.frameBundle_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.framed_entries_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.framed_closed
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.framed_goals_fof
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.framed_objects_covered
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.objectsOf_nodup
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.objectIds_nodup
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.distinctItems_models

end Fang.TptpCandidate.Roles.Bundle.V2
