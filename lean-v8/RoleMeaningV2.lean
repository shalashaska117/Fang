/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed bundle meanings over the revision-2 role framer, and the refutation theorems that prove them. The meanings keep `FramerV2.NamedSeparated`, `FramerV2.wellShaped` and the coverage expansion. -/
import RoleFramerV2

namespace Fang.TptpCandidate.Roles.Bundle.V2
open FullFof Numeric

/-- The bundle framed with roles by the given tokenizer, well shaped and expanded. -/
def Expanded (tokenize : Tokenizer) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat)
    (bundle : RoleBundle) (items : List Coverage.Item) : Prop :=
  frameBundle tokenize files maximum = .ok bundle ∧ Coverage.FramerV2.wellShaped (forget bundle) fuel = true ∧
    Coverage.expand (forget bundle) fuel = .ok items

/-- One selected original conjecture, identified by its bundle item, follows from the selected premises in every model that keeps distinct objects apart. -/
def GoalEntailed (tokenize : Tokenizer) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat)
    (item : Coverage.Item) : Prop :=
  ∃ bundle items entry, Expanded tokenize files maximum fuel bundle items ∧ (item, entry) ∈ goalItems bundle items ∧
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model entry.original.body.formula

/-- The statement for SZS Theorem: at least one selected original conjecture, and every one is entailed. -/
def ByteTheorem (tokenize : Tokenizer) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, Expanded tokenize files maximum fuel bundle items ∧ goalItems bundle items ≠ [] ∧
    ∀ pair ∈ goalItems bundle items, ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model pair.2.original.body.formula

/-- The statement for SZS Unsatisfiable: no selected conjecture, and the positive inputs have no model that keeps distinct objects apart. -/
def ByteUnsatisfiable (tokenize : Tokenizer) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, Expanded tokenize files maximum fuel bundle items ∧ goalItems bundle items = [] ∧
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (objectsOf bundle items) →
      ¬ Roles.AllHold (Bytes.sentence (D := D)) (Roles.positiveInputs (Bytes.source (entriesOf bundle items))) model

theorem expanded_unique {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle other : RoleBundle} {items others : List Coverage.Item}
    (first : Expanded tokenize files maximum fuel bundle items) (second : Expanded tokenize files maximum fuel other others) :
    bundle = other ∧ items = others := by
  have same : bundle = other := Except.ok.inj (first.1.symm.trans second.1)
  subst same
  exact ⟨rfl, Except.ok.inj (first.2.2.symm.trans second.2.2)⟩

/-- One goal task, refuted together with the generated disequalities, proves that goal from the selected premises in every model that keeps distinct objects apart. -/
theorem goal_entailed_of_refuted {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    {before after : List RoleRow} {goal : RoleRow} {task : List SignedNumeric}
    (expanded : Expanded tokenize files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (split : input.rows = before ++ goal :: after) (built : goalTask before goal after = some task)
    (refuted : ¬ TaskSatisfiable input (task ++ distinctItems input bundle items)) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model goal.declaration.original := by
  intro D inhabited model separated premisesHold
  let _ : Nonempty D := inhabited
  apply Classical.byContradiction
  intro fails
  apply refuted
  refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
  rw [taskModels_append]
  exact ⟨(goalTask_models read (framed_closed expanded.1 items) split built (model_toNumeric model _ _)).mpr
      ⟨premisesHold, (Roles.negative_holds _ _).mpr fails⟩,
    distinctItems_models expanded.1 read model separated⟩

/-- The goal at index `index` among the selected conjectures is the item at that index of `goalItems`; a refuted task for it proves `GoalEntailed` for that item. -/
theorem goal_item_entailed {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    {index : Nat} {before after : List RoleRow} {goal : RoleRow} {item : Coverage.Item}
    {entry : Bytes.Entry} {task : List SignedNumeric}
    (expanded : Expanded tokenize files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (selected : ((splits input.rows).filter (fun split => decide (split.2.1.role = .conjecture)))[index]? =
      some (before, goal, after))
    (identity : (goalItems bundle items)[index]? = some (item, entry))
    (built : goalTask before goal after = some task)
    (refuted : ¬ TaskSatisfiable input (task ++ distinctItems input bundle items)) :
    GoalEntailed tokenize files maximum fuel item := by
  have member : (before, goal, after) ∈ splits input.rows :=
    (List.mem_filter.mp (List.mem_of_getElem? selected)).1
  have split := mem_splits.mp member
  have same : goal.declaration = entryDeclaration entry := by
    have mapped := congrArg (fun list => list[index]?) (goal_rows_items read)
    simp only [List.getElem?_map, selected, identity, Option.map_some, Option.some.injEq] at mapped
    exact mapped
  refine ⟨bundle, items, entry, expanded, List.mem_of_getElem? identity, ?_⟩
  intro D inhabited model separated premisesHold
  have holds := goal_entailed_of_refuted expanded read split built refuted D inhabited model separated premisesHold
  rw [same] at holds
  exact holds

/-- The no-goal task, refuted together with the generated disequalities, proves `ByteUnsatisfiable` when no conjecture is selected. -/
theorem unsatisfiable_of_refuted {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    (expanded : Expanded tokenize files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (noGoals : goalItems bundle items = [])
    (refuted : ¬ TaskSatisfiable input (inputsTask input ++ distinctItems input bundle items)) :
    ByteUnsatisfiable tokenize files maximum fuel := by
  refine ⟨bundle, items, expanded, noGoals, ?_⟩
  intro D inhabited model separated holds
  let _ : Nonempty D := inhabited
  apply refuted
  refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
  rw [taskModels_append]
  exact ⟨(inputsTask_models read (framed_closed expanded.1 items) (model_toNumeric model _ _)).mpr holds,
    distinctItems_models expanded.1 read model separated⟩

theorem goalItems_entry {bundle : RoleBundle} {items : List Coverage.Item} {item : Coverage.Item}
    {entry : Bytes.Entry} (member : (item, entry) ∈ goalItems bundle items) :
    roleStatementAt bundle item = some (.formula entry) := by
  simp only [goalItems, List.mem_filter, List.mem_filterMap] at member
  obtain ⟨⟨other, _, found⟩, _⟩ := member
  cases statementAt : roleStatementAt bundle other with
  | none => simp [statementAt] at found
  | some statement =>
    cases statement with
    | directive parts selection => simp [statementAt] at found
    | formula value =>
      simp only [statementAt, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact statementAt

/-- `ByteTheorem` from at least one selected conjecture and `GoalEntailed` for every goal item. -/
theorem byteTheorem_of_entailed {tokenize : Tokenizer} {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item}
    (expanded : Expanded tokenize files maximum fuel bundle items) (nonempty : goalItems bundle items ≠ [])
    (entailed : ∀ pair ∈ goalItems bundle items, GoalEntailed tokenize files maximum fuel pair.1) :
    ByteTheorem tokenize files maximum fuel := by
  refine ⟨bundle, items, expanded, nonempty, ?_⟩
  intro ⟨item, value⟩ member D inhabited model separated premisesHold
  obtain ⟨other, others, entry, otherExpanded, otherMember, entails⟩ := entailed (item, value) member
  obtain ⟨rfl, rfl⟩ := expanded_unique expanded otherExpanded
  have first := goalItems_entry otherMember
  have second := goalItems_entry member
  rw [first] at second
  simp only [Option.some.injEq, RoleStatement.formula.injEq] at second
  rw [← second]
  exact entails D inhabited model separated premisesHold

#print axioms Fang.TptpCandidate.Roles.Bundle.V2.expanded_unique
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.goal_entailed_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.goal_item_entailed
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.unsatisfiable_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.goalItems_entry
#print axioms Fang.TptpCandidate.Roles.Bundle.V2.byteTheorem_of_entailed

end Fang.TptpCandidate.Roles.Bundle.V2
