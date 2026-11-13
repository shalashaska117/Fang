/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Premise monotonicity over bundles decoded at any formula depth. -/
import RoleCitedRead
import RoleReplayDepth

namespace Fang.TptpCandidate.Roles.Bundle.V3.Depth
open FullFof Numeric

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

end Fang.TptpCandidate.Roles.Bundle.V3.Depth
