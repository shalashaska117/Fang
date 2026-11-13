/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The kept part of an expansion for a task whose certificate cites its premises: the cited items and the selected goal's item, in expansion order. The kept items are a sublist of the expanded items, so every lemma here is monotonicity: a model of all premises is a model of the kept premises, a model of all positive inputs is a model of the kept ones, and distinct objects kept apart in the whole expansion are kept apart in its kept part. -/
import RoleReplayLimit

namespace Fang.TptpCandidate.Roles.Bundle.V3
open FullFof Numeric

/-- The expanded items a cited task keeps, in expansion order: the cited items and `extra`. -/
def keptItems (items cited : List Coverage.Item) (extra : Option Coverage.Item) : List Coverage.Item :=
  items.filter fun item => cited.contains item || extra == some item

theorem keptItems_sublist (items cited : List Coverage.Item) (extra : Option Coverage.Item) :
    (keptItems items cited extra).Sublist items :=
  List.filter_sublist

/-- Citing every expanded item keeps every item. -/
theorem keptItems_all (items : List Coverage.Item) (extra : Option Coverage.Item) :
    keptItems items items extra = items := by
  unfold keptItems
  rw [List.filter_eq_self]
  intro item member
  simp [member]

theorem entriesOf_sublist {bundle : RoleBundle} {kept items : List Coverage.Item} (sub : kept.Sublist items) :
    (entriesOf bundle kept).Sublist (entriesOf bundle items) := by
  unfold entriesOf
  exact sub.filterMap _

theorem declarationsOf_sublist {bundle : RoleBundle} {kept items : List Coverage.Item} (sub : kept.Sublist items) :
    (Coverage.declarationsOf (forget bundle) kept).Sublist (Coverage.declarationsOf (forget bundle) items) := by
  unfold Coverage.declarationsOf
  exact sub.filterMap _

/-- Every distinct object of the kept part is a distinct object of the whole expansion. -/
theorem objectsOf_kept {bundle : RoleBundle} {kept items : List Coverage.Item} (sub : kept.Sublist items)
    {label : String} (member : label ∈ V2.objectsOf bundle kept) : label ∈ V2.objectsOf bundle items := by
  unfold V2.objectsOf Coverage.FramerV2.objectNames at member ⊢
  rw [List.mem_eraseDups] at member ⊢
  simp only [List.mem_filterMap, List.mem_flatMap] at member ⊢
  obtain ⟨symbol, ⟨formula, formulaMember, present⟩, chosen⟩ := member
  have larger : formula ∈ source (Coverage.declarationsOf (forget bundle) items) := by
    unfold source at formulaMember ⊢
    exact ((declarationsOf_sublist sub).map _).subset formulaMember
  exact ⟨symbol, ⟨formula, larger, present⟩, chosen⟩

theorem separated_kept {bundle : RoleBundle} {kept items : List Coverage.Item} (sub : kept.Sublist items)
    {D : Type} {model : Source.Interpretation D}
    (separated : Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items)) :
    Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle kept) :=
  fun left leftMember right rightMember =>
    separated left (objectsOf_kept sub leftMember) right (objectsOf_kept sub rightMember)

theorem premises_hold_kept {bundle : RoleBundle} {kept items : List Coverage.Item} (sub : kept.Sublist items)
    {D : Type} {model : Source.Interpretation D}
    (holds : Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model) :
    Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle kept))) model := by
  intro declaration member
  apply holds declaration
  simp only [Roles.premises, Bytes.source, List.mem_filter, List.mem_map] at member ⊢
  obtain ⟨⟨value, valueMember, rfl⟩, role⟩ := member
  exact ⟨⟨value, (entriesOf_sublist sub).subset valueMember, rfl⟩, role⟩

theorem inputs_hold_kept {bundle : RoleBundle} {kept items : List Coverage.Item} (sub : kept.Sublist items)
    {D : Type} {model : Source.Interpretation D}
    (holds : Roles.AllHold (Bytes.sentence (D := D))
      (Roles.positiveInputs (Bytes.source (entriesOf bundle items))) model) :
    Roles.AllHold (Bytes.sentence (D := D)) (Roles.positiveInputs (Bytes.source (entriesOf bundle kept))) model := by
  intro declaration member
  apply holds declaration
  simp only [Roles.positiveInputs, Bytes.source, List.mem_filter, List.mem_map] at member ⊢
  obtain ⟨⟨value, valueMember, rfl⟩, role⟩ := member
  exact ⟨⟨value, (entriesOf_sublist sub).subset valueMember, rfl⟩, role⟩

/-! Refutations of a kept task. They are `goal_entailed_of_refuted` and `unsatisfiable_of_refuted` over any item list of a sound bundle, which need not be the whole expansion. -/

theorem goal_holds_of_refuted {bundle : RoleBundle} (sound : SoundBundle bundle) {kept : List Coverage.Item}
    {input : SignedInput} {before after : List RoleRow} {goal : RoleRow} {task : List SignedNumeric}
    (read : readSigned (entriesOf bundle kept) = some input)
    (split : input.rows = before ++ goal :: after) (built : goalTask before goal after = some task)
    (refuted : ¬ TaskSatisfiable input (task ++ V2.distinctItems input bundle kept)) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle kept) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle kept))) model →
        Bytes.sentence model goal.declaration.original := by
  intro D inhabited model separated premisesHold
  let _ : Nonempty D := inhabited
  apply Classical.byContradiction
  intro fails
  apply refuted
  refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
  rw [taskModels_append]
  exact ⟨(goalTask_models read (entries_closed sound kept) split built (model_toNumeric model _ _)).mpr
      ⟨premisesHold, (Roles.negative_holds _ _).mpr fails⟩,
    distinctItems_models sound read model separated⟩

theorem inputs_fail_of_refuted {bundle : RoleBundle} (sound : SoundBundle bundle) {kept : List Coverage.Item}
    {input : SignedInput} (read : readSigned (entriesOf bundle kept) = some input)
    (refuted : ¬ TaskSatisfiable input (inputsTask input ++ V2.distinctItems input bundle kept)) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle kept) →
      ¬ Roles.AllHold (Bytes.sentence (D := D)) (Roles.positiveInputs (Bytes.source (entriesOf bundle kept))) model := by
  intro D inhabited model separated holds
  let _ : Nonempty D := inhabited
  apply refuted
  refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
  rw [taskModels_append]
  exact ⟨(inputsTask_models read (entries_closed sound kept) (model_toNumeric model _ _)).mpr holds,
    distinctItems_models sound read model separated⟩

/-- A refuted kept goal task proves the goal from the premises of every item list that contains the kept items. -/
theorem goal_holds_of_refuted_lifted {bundle : RoleBundle} (sound : SoundBundle bundle)
    {kept items : List Coverage.Item} (sub : kept.Sublist items)
    {input : SignedInput} {before after : List RoleRow} {goal : RoleRow} {task : List SignedNumeric}
    (read : readSigned (entriesOf bundle kept) = some input)
    (split : input.rows = before ++ goal :: after) (built : goalTask before goal after = some task)
    (refuted : ¬ TaskSatisfiable input (task ++ V2.distinctItems input bundle kept)) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model goal.declaration.original :=
  fun D inhabited model separated premisesHold =>
    goal_holds_of_refuted sound read split built refuted D inhabited model (separated_kept sub separated)
      (premises_hold_kept sub premisesHold)

/-- A refuted kept inputs task proves that every item list containing the kept items has no model of its positive inputs. -/
theorem inputs_fail_of_refuted_lifted {bundle : RoleBundle} (sound : SoundBundle bundle)
    {kept items : List Coverage.Item} (sub : kept.Sublist items) {input : SignedInput}
    (read : readSigned (entriesOf bundle kept) = some input)
    (refuted : ¬ TaskSatisfiable input (inputsTask input ++ V2.distinctItems input bundle kept)) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items) →
      ¬ Roles.AllHold (Bytes.sentence (D := D)) (Roles.positiveInputs (Bytes.source (entriesOf bundle items))) model :=
  fun D inhabited model separated holds =>
    inputs_fail_of_refuted sound read refuted D inhabited model (separated_kept sub separated)
      (inputs_hold_kept sub holds)

#print axioms Fang.TptpCandidate.Roles.Bundle.V3.keptItems_sublist
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.keptItems_all
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.entriesOf_sublist
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.declarationsOf_sublist
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.objectsOf_kept
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.separated_kept
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.premises_hold_kept
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.inputs_hold_kept
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.goal_holds_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.inputs_fail_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.goal_holds_of_refuted_lifted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.inputs_fail_of_refuted_lifted

end Fang.TptpCandidate.Roles.Bundle.V3
