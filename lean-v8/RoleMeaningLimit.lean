/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed bundle meanings and refutation theorems for any sound frame function. They are the revision-2 statements with `V2.frameBundle tokenize` replaced by a frame parameter; the facts about framed entries need only `SoundBundle`. -/
import RoleFramerLimit

namespace Fang.TptpCandidate.Roles.Bundle.V3
open FullFof Numeric

abbrev Frame := List (Coverage.Key × List UInt8) → Nat → Except Error RoleBundle

/-! Entries of a sound bundle. -/

theorem entries_sound {bundle : RoleBundle} (sound : SoundBundle bundle) (items : List Coverage.Item)
    {value : Bytes.Entry} (member : value ∈ entriesOf bundle items) : V2.RoleDecoded value := by
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
        exact sound file (List.mem_of_getElem? fileAt) decoded (List.mem_of_getElem? statementAt)

theorem entries_closed {bundle : RoleBundle} (sound : SoundBundle bundle) (items : List Coverage.Item) :
    Bytes.Closed (entriesOf bundle items) := by
  intro value member
  obtain ⟨seen, endOffset, tokens, decoded, _⟩ := entries_sound sound items member
  exact Bytes.declaration_closed decoded

theorem objects_covered {bundle : RoleBundle} (sound : SoundBundle bundle) (items : List Coverage.Item)
    {input : Integration.NumericInput}
    (encoded : Integration.readInput (Coverage.declarationsOf (forget bundle) items) = some input) :
    ∀ label ∈ V2.objectsOf bundle items, (label, 0) ∈ input.functions := by
  intro label member
  rw [(Integration.readInput_tables encoded).1]
  simp only [V2.objectsOf, Coverage.FramerV2.objectNames, List.mem_eraseDups, List.mem_filterMap,
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
    obtain ⟨_, _, _, _, used⟩ := entries_sound sound items entryAt
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

theorem objectIds_nodup {bundle : RoleBundle} (sound : SoundBundle bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input) :
    (V2.objectIds input bundle items).Nodup := by
  have covered := objects_covered sound items (read_tables read)
  apply List.pairwise_map.mpr
  refine (V2.objectsOf_nodup bundle items).imp_of_mem ?_
  intro first second firstMember secondMember different same
  exact different (Prod.mk.inj (Arity.id_injective (covered first firstMember)
    (covered second secondMember) same)).1

theorem distinctItems_models {bundle : RoleBundle} (sound : SoundBundle bundle) {items : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle items) = some input)
    {D : Type} [Nonempty D] (model : Source.Interpretation D)
    (separated : Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items)) :
    TaskModels (FullFof.toNumeric model input.functions input.predicates) (V2.distinctItems input bundle items) := by
  have covered := objects_covered sound items (read_tables read)
  have agreement := model_toNumeric model input.functions input.predicates
  have numeric := (Coverage.FramerV2.separated_iff agreement covered).mp separated
  have nodup := objectIds_nodup sound read
  intro item member
  obtain ⟨declaration, present, rfl⟩ := List.mem_map.mp member
  rw [positive_holds]
  obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp present
  obtain ⟨left, right⟩ := pair
  obtain ⟨leftMember, rightMember, different⟩ := Coverage.pairs_mem pairMember
  apply (Coverage.disequality_models (Arity.toNumeric model input.functions input.predicates)
    input.predicates.length left right).mpr
  exact numeric left leftMember right rightMember (different nodup)

/-! Meanings for a frame function. -/

def Expanded (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat)
    (bundle : RoleBundle) (items : List Coverage.Item) : Prop :=
  frame files maximum = .ok bundle ∧ Coverage.FramerV2.wellShaped (forget bundle) fuel = true ∧
    Coverage.expand (forget bundle) fuel = .ok items

def GoalEntailed (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat)
    (item : Coverage.Item) : Prop :=
  ∃ bundle items entry, Expanded frame files maximum fuel bundle items ∧ (item, entry) ∈ goalItems bundle items ∧
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model entry.original.body.formula

def ByteTheorem (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, Expanded frame files maximum fuel bundle items ∧ goalItems bundle items ≠ [] ∧
    ∀ pair ∈ goalItems bundle items, ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model pair.2.original.body.formula

def ByteUnsatisfiable (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, Expanded frame files maximum fuel bundle items ∧ goalItems bundle items = [] ∧
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items) →
      ¬ Roles.AllHold (Bytes.sentence (D := D)) (Roles.positiveInputs (Bytes.source (entriesOf bundle items))) model

/-- With the revision-2 role framer as the frame, the meanings are the revision-2 ones. -/
theorem expanded_revision_two (tokenize : V2.Tokenizer) :
    Expanded (V2.frameBundle tokenize) = V2.Expanded tokenize := rfl

theorem expanded_unique {frame : Frame} {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle other : RoleBundle} {items others : List Coverage.Item}
    (first : Expanded frame files maximum fuel bundle items) (second : Expanded frame files maximum fuel other others) :
    bundle = other ∧ items = others := by
  have same : bundle = other := Except.ok.inj (first.1.symm.trans second.1)
  subst same
  exact ⟨rfl, Except.ok.inj (first.2.2.symm.trans second.2.2)⟩

theorem goal_entailed_of_refuted {frame : Frame} (frameSound : FrameSound frame)
    {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    {before after : List RoleRow} {goal : RoleRow} {task : List SignedNumeric}
    (expanded : Expanded frame files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (split : input.rows = before ++ goal :: after) (built : goalTask before goal after = some task)
    (refuted : ¬ TaskSatisfiable input (task ++ V2.distinctItems input bundle items)) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model goal.declaration.original := by
  have sound := frameSound expanded.1
  intro D inhabited model separated premisesHold
  let _ : Nonempty D := inhabited
  apply Classical.byContradiction
  intro fails
  apply refuted
  refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
  rw [taskModels_append]
  exact ⟨(goalTask_models read (entries_closed sound items) split built (model_toNumeric model _ _)).mpr
      ⟨premisesHold, (Roles.negative_holds _ _).mpr fails⟩,
    distinctItems_models sound read model separated⟩

theorem goal_item_entailed {frame : Frame} (frameSound : FrameSound frame)
    {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    {index : Nat} {before after : List RoleRow} {goal : RoleRow} {item : Coverage.Item}
    {entry : Bytes.Entry} {task : List SignedNumeric}
    (expanded : Expanded frame files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (selected : ((splits input.rows).filter (fun split => decide (split.2.1.role = .conjecture)))[index]? =
      some (before, goal, after))
    (identity : (goalItems bundle items)[index]? = some (item, entry))
    (built : goalTask before goal after = some task)
    (refuted : ¬ TaskSatisfiable input (task ++ V2.distinctItems input bundle items)) :
    GoalEntailed frame files maximum fuel item := by
  have member : (before, goal, after) ∈ splits input.rows :=
    (List.mem_filter.mp (List.mem_of_getElem? selected)).1
  have split := mem_splits.mp member
  have same : goal.declaration = entryDeclaration entry := by
    have mapped := congrArg (fun list => list[index]?) (goal_rows_items read)
    simp only [List.getElem?_map, selected, identity, Option.map_some, Option.some.injEq] at mapped
    exact mapped
  refine ⟨bundle, items, entry, expanded, List.mem_of_getElem? identity, ?_⟩
  intro D inhabited model separated premisesHold
  have holds := goal_entailed_of_refuted frameSound expanded read split built refuted D inhabited model separated
    premisesHold
  rw [same] at holds
  exact holds

theorem unsatisfiable_of_refuted {frame : Frame} (frameSound : FrameSound frame)
    {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    (expanded : Expanded frame files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (noGoals : goalItems bundle items = [])
    (refuted : ¬ TaskSatisfiable input (inputsTask input ++ V2.distinctItems input bundle items)) :
    ByteUnsatisfiable frame files maximum fuel := by
  have sound := frameSound expanded.1
  refine ⟨bundle, items, expanded, noGoals, ?_⟩
  intro D inhabited model separated holds
  let _ : Nonempty D := inhabited
  apply refuted
  refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
  rw [taskModels_append]
  exact ⟨(inputsTask_models read (entries_closed sound items) (model_toNumeric model _ _)).mpr holds,
    distinctItems_models sound read model separated⟩

theorem byteTheorem_of_entailed {frame : Frame} {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item}
    (expanded : Expanded frame files maximum fuel bundle items) (nonempty : goalItems bundle items ≠ [])
    (entailed : ∀ pair ∈ goalItems bundle items, GoalEntailed frame files maximum fuel pair.1) :
    ByteTheorem frame files maximum fuel := by
  refine ⟨bundle, items, expanded, nonempty, ?_⟩
  intro ⟨item, value⟩ member D inhabited model separated premisesHold
  obtain ⟨other, others, entry, otherExpanded, otherMember, entails⟩ := entailed (item, value) member
  obtain ⟨rfl, rfl⟩ := expanded_unique expanded otherExpanded
  have first := V2.goalItems_entry otherMember
  have second := V2.goalItems_entry member
  rw [first] at second
  simp only [Option.some.injEq, RoleStatement.formula.injEq] at second
  rw [← second]
  exact entails D inhabited model separated premisesHold

#print axioms Fang.TptpCandidate.Roles.Bundle.V3.entries_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.entries_closed
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.objects_covered
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.objectIds_nodup
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.distinctItems_models
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.expanded_revision_two
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.expanded_unique
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.goal_entailed_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.goal_item_entailed
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.unsatisfiable_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.byteTheorem_of_entailed

end Fang.TptpCandidate.Roles.Bundle.V3
