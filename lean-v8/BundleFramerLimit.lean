/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The bundle framer (revision 2) with the per-file formula limit as a parameter. `frameBundle limit` is `FramerV2.frameBundle` with `limit` in place of 1,000, and `frameBundle_accepted` proves the two equal at 1,000. Soundness is stated for any frame function: `FrameSound frame` says that every formula statement of a framed bundle is an accepted-decoder record, and the bundle meaning, the closure and object facts and the refutation endpoint take the frame as a parameter. With `FramerV2.frameBundle` as the frame the meaning is `FramerV2.ByteBundleSatisfiable`. The structure follows the role framer's `RoleFramerLimit` and `RoleMeaningLimit`. This module imports no extracted code. -/
import BundleFramerNodup

namespace Fang.TptpCandidate.FullFof.Coverage.FramerLimit

open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2 (Piece splitStatement keyword directive formulaRecord
  Decoded formulaRecord_sound wellShaped objectNames NamedSeparated isObject objectsWellUsed objectNames_nodup)

abbrev Frame := List (Key × List UInt8) → Nat → Except Error Bundle

/-- Every formula statement of the bundle is an accepted-decoder record. -/
def SoundBundle (bundle : Bundle) : Prop :=
  ∀ file ∈ bundle, ∀ value, Statement.formula value ∈ file.statements → Decoded value

/-- A frame function whose every result is a sound bundle. -/
def FrameSound (frame : Frame) : Prop :=
  ∀ {files maximum bundle}, frame files maximum = .ok bundle → SoundBundle bundle

/-! The list framer with the limit as a parameter. -/

/-- `FramerV2.statements` with `limit` in place of 1,000. -/
def statements (limit : Nat) : Nat → List Name → Nat → List Piece → Except Error (List Statement)
  | 0, _, endOffset, _ => .error ⟨.resource, endOffset⟩
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, first :: more =>
    if seen.length ≥ limit then .error ⟨.resource, first.start⟩
    else
      let split := splitStatement 0 [] (first :: more)
      match keyword split.1 with
      | some "include" =>
        match directive split.1 with
        | .error failure => .error failure
        | .ok (parts, selection) =>
          match statements limit fuel seen endOffset split.2 with
          | .error failure => .error failure
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecord seen endOffset split.1 with
        | .error failure => .error failure
        | .ok value =>
          match statements limit fuel (value.name :: seen) endOffset split.2 with
          | .error failure => .error failure
          | .ok tail => .ok (.formula value :: tail)

theorem statements_accepted : ∀ (fuel : Nat) (seen : List Name) (endOffset : Nat) (pieces : List Piece),
    statements 1000 fuel seen endOffset pieces = FramerV2.statements fuel seen endOffset pieces
  | 0, _, _, _ => by
    unfold statements FramerV2.statements
    rfl
  | fuel + 1, seen, endOffset, [] => by
    unfold statements FramerV2.statements
    rfl
  | fuel + 1, seen, endOffset, first :: more => by
    unfold statements FramerV2.statements
    simp only [statements_accepted]
    rfl

def frameFile (limit : Nat) (bytes : List UInt8) (maximum : Nat) : Except Error (List Statement) :=
  match FramerV2.tokenize bytes maximum with
  | .error failure => .error failure
  | .ok pieces => statements limit (pieces.length + 1) [] bytes.length pieces

def frameBundle (limit : Nat) : List (Key × List UInt8) → Nat → Except Error Bundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFile limit bytes maximum with
    | .error failure => .error failure
    | .ok framed => match frameBundle limit rest maximum with
      | .error failure => .error failure
      | .ok others => .ok (⟨key, framed⟩ :: others)

/-- With limit 1,000 the list framer is framer revision 2. -/
theorem frameBundle_accepted : ∀ (files : List (Key × List UInt8)) (maximum : Nat),
    frameBundle 1000 files maximum = FramerV2.frameBundle files maximum
  | [], _ => rfl
  | (key, bytes) :: rest, maximum => by
    simp only [frameBundle, FramerV2.frameBundle, frameFile, FramerV2.frameFile, statements_accepted,
      frameBundle_accepted rest maximum]
    rfl

theorem statements_sound (limit : Nat) : ∀ fuel seen endOffset pieces result,
    statements limit fuel seen endOffset pieces = .ok result →
      ∀ value, Statement.formula value ∈ result → Decoded value := by
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

theorem frameBundle_sound (limit : Nat) : FrameSound (frameBundle limit) := by
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

/-- Framer revision 2 is a sound frame. -/
theorem revision_two_sound : FrameSound FramerV2.frameBundle :=
  fun success => FramerV2.frameBundle_sound success

/-! Declarations of a sound bundle: the facts of `BundleFramerSound`, `BundleFramerPremises` and
    `BundleFramerNodup` with `SoundBundle` in place of a successful revision-2 framing. -/

theorem declarations_sound {bundle : Bundle} (sound : SoundBundle bundle) (items : List Item)
    {value : Declaration} (member : value ∈ declarationsOf bundle items) : Decoded value := by
  simp only [declarationsOf, List.mem_filterMap] at member
  obtain ⟨item, _, found⟩ := member
  cases at_item : statementAt bundle item with
  | none => simp [at_item] at found
  | some statement =>
    cases statement with
    | directive parts selection => simp [at_item] at found
    | formula decoded =>
      simp only [at_item, Option.some.injEq] at found
      subst found
      simp only [statementAt, bind, Option.bind] at at_item
      cases fileAt : bundle[item.1]? with
      | none => simp [fileAt] at at_item
      | some file =>
        simp only [fileAt] at at_item
        exact sound file (List.mem_of_getElem? fileAt) decoded (List.mem_of_getElem? at_item)

theorem declarations_closed {bundle : Bundle} (sound : SoundBundle bundle) (items : List Item) :
    Grammar.Closed (declarationsOf bundle items) := by
  intro value member
  obtain ⟨seen, endOffset, tokens, decoded, _⟩ := declarations_sound sound items member
  exact CnfBoolean.declaration_closed decoded

theorem objects_covered {bundle : Bundle} (sound : SoundBundle bundle) (items : List Item)
    {input : Integration.NumericInput}
    (encoded : Integration.readInput (declarationsOf bundle items) = some input) :
    ∀ label ∈ objectNames (declarationsOf bundle items), (label, 0) ∈ input.functions := by
  intro label member
  rw [(Integration.readInput_tables encoded).1]
  simp only [objectNames, List.mem_eraseDups, List.mem_filterMap, List.mem_flatMap] at member
  obtain ⟨symbol, ⟨formula, formulaMember, present⟩, chosen⟩ := member
  by_cases object : isObject symbol.1 = true
  · simp only [object, ↓reduceIte, Option.some.injEq] at chosen
    subst chosen
    simp only [source, List.mem_map, Function.comp] at formulaMember
    obtain ⟨value, valueMember, rfl⟩ := formulaMember
    obtain ⟨_, _, _, _, used⟩ := declarations_sound sound items valueMember
    have arity : symbol.2 = 0 := by
      simp only [objectsWellUsed, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false] at used
      have := used.2 symbol present
      simp only [object, bne_iff_ne, ne_eq] at this
      exact Classical.byContradiction fun different => this ⟨trivial, different⟩
    have inSource : value.body.formula ∈ source (declarationsOf bundle items) :=
      List.mem_map.mpr ⟨value, valueMember, rfl⟩
    have covered := (collected_covered inSource).functions symbol present
    have shape : symbol = (symbol.1, 0) := Prod.ext rfl arity
    rw [← shape]
    exact covered
  · simp [object] at chosen

theorem object_ids_nodup {bundle : Bundle} (sound : SoundBundle bundle) (items : List Item)
    {input : Integration.NumericInput}
    (encoded : Integration.readInput (declarationsOf bundle items) = some input) :
    ((objectNames (declarationsOf bundle items)).map
      fun label => Arity.id input.functions (label, 0)).Nodup := by
  have covered := objects_covered sound items encoded
  apply List.pairwise_map.mpr
  refine (objectNames_nodup (declarationsOf bundle items)).imp_of_mem ?_
  intro first second firstMember secondMember different same
  exact different (Prod.mk.inj (Arity.id_injective (covered first firstMember)
    (covered second secondMember) same)).1

/-! The meaning for a frame function. -/

/-- `FramerV2.ByteBundleSatisfiable` with the frame as a parameter. -/
def ByteBundleSatisfiable (frame : Frame) (files : List (Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, frame files maximum = .ok bundle ∧ wellShaped bundle fuel = true ∧
    expand bundle fuel = .ok items ∧
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Models (source (declarationsOf bundle items)) model ∧
      NamedSeparated model (objectNames (declarationsOf bundle items))

/-- With framer revision 2 as the frame, the meaning is the revision-2 one. -/
theorem byteBundleSatisfiable_revision_two :
    ByteBundleSatisfiable FramerV2.frameBundle = FramerV2.ByteBundleSatisfiable := rfl

theorem byte_bundle_unsat {frame : Frame} {files : List (Key × List UInt8)} {maximum fuel : Nat}
    {bundle : Bundle} {items : List Item} (framed : frame files maximum = .ok bundle)
    (expanded : expand bundle fuel = .ok items)
    (refuted : ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Models (source (declarationsOf bundle items)) model →
        ¬ NamedSeparated model (objectNames (declarationsOf bundle items))) :
    ¬ ByteBundleSatisfiable frame files maximum fuel := by
  rintro ⟨bundle', items', framed', _, expanded', D, inhabited, model, holds, separated⟩
  rw [framed] at framed'
  cases framed'
  rw [expanded] at expanded'
  cases expanded'
  exact refuted D inhabited model holds separated

/-- The byte-bundle endpoint for a sound frame: a successful framing, expansion and `readInput`, and a
    refutation of the numeric problem with the generated pairwise disequalities, refute the bundle. -/
theorem byte_bundle_unsat_of_refutation {frame : Frame} (frameSound : FrameSound frame)
    {files : List (Key × List UInt8)} {maximum fuel : Nat}
    {bundle : Bundle} {items : List Item} {input : Integration.NumericInput}
    (framed : frame files maximum = .ok bundle) (expanded : expand bundle fuel = .ok items)
    (encoded : Integration.readInput (declarationsOf bundle items) = some input)
    (refuted : ¬ ReservedSatisfiable input.predicates.length
      (input.declarations ++ distinctAxioms input.predicates.length
        ((objectNames (declarationsOf bundle items)).map fun label => Arity.id input.functions (label, 0)))) :
    ¬ ByteBundleSatisfiable frame files maximum fuel := by
  have sound := frameSound framed
  apply byte_bundle_unsat framed expanded
  intro D inhabited model holds separated
  exact distinct_unsat _ _ (object_ids_nodup sound items encoded) refuted
    ((FramerV2.objects_distinct_satisfiable encoded (declarations_closed sound items)
      (objects_covered sound items encoded)).mp ⟨D, inhabited, model, holds, separated⟩)

#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.statements_accepted
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.frameBundle_accepted
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.statements_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.frameBundle_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.revision_two_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.declarations_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.declarations_closed
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.objects_covered
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.object_ids_nodup
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.byteBundleSatisfiable_revision_two
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.byte_bundle_unsat
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.byte_bundle_unsat_of_refutation

end Fang.TptpCandidate.FullFof.Coverage.FramerLimit
