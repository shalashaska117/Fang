/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Goal identities by bundle item, and the object-identity premise derived from the complete tables. -/
import BundleRoles

namespace Fang.TptpCandidate.Roles.Bundle
open FullFof Numeric

/-! The object IDs are duplicate-free. -/

theorem eraseDups_loop_nodup {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (rest accumulated : List α), accumulated.Nodup →
      (List.eraseDupsBy.loop (· == ·) rest accumulated).Nodup := by
  intro rest
  induction rest with
  | nil =>
    intro accumulated nodup
    simp only [List.eraseDupsBy.loop]
    exact List.pairwise_reverse.mpr (nodup.imp fun different same => different same.symm)
  | cons first more ih =>
    intro accumulated nodup
    unfold List.eraseDupsBy.loop
    split
    · exact ih accumulated nodup
    · rename_i absent
      apply ih
      refine List.nodup_cons.mpr ⟨fun member => ?_, nodup⟩
      have found : accumulated.any (fun other => first == other) = true :=
        List.any_eq_true.mpr ⟨first, member, beq_self_eq_true first⟩
      rw [found] at absent
      cases absent

theorem objectsOf_nodup (bundle : RoleBundle) (items : List Coverage.Item) : (objectsOf bundle items).Nodup := by
  unfold objectsOf Coverage.Framer.objectNames List.eraseDups List.eraseDupsBy
  exact eraseDups_loop_nodup _ [] List.nodup_nil

/-- Different object names get different IDs in the complete function table. -/
theorem objectIds_nodup {files : List (Coverage.Key × List UInt8)} {maximum : Nat} {bundle : RoleBundle}
    (framed : frameBundle files maximum = .ok bundle) {items : List Coverage.Item} {input : SignedInput}
    (read : readSigned (entriesOf bundle items) = some input) : (objectIds input bundle items).Nodup := by
  have covered := framed_objects_covered framed items (read_tables read)
  apply List.pairwise_map.mpr
  refine (objectsOf_nodup bundle items).imp_of_mem ?_
  intro first second firstMember secondMember different same
  exact different (Prod.mk.inj (Arity.id_injective (covered first firstMember)
    (covered second secondMember) same)).1

/-! The refutation theorems with the derived premise. -/

theorem goal_entailed_of_refuted {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    {before after : List RoleRow} {goal : RoleRow} {task : List SignedNumeric}
    (expanded : Expanded files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (split : input.rows = before ++ goal :: after) (built : goalTask before goal after = some task)
    (refuted : ¬ TaskSatisfiable input (task ++ distinctItems input bundle items)) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.Framer.NamedSeparated model (objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model goal.declaration.original :=
  goal_refuted_entails expanded read split built (objectIds_nodup expanded.1 read) refuted

theorem inputs_unsat_of_refuted {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    (expanded : Expanded files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (refuted : ¬ TaskSatisfiable input (inputsTask input ++ distinctItems input bundle items)) :
    ¬ ByteBundleInputsSatisfiable files maximum fuel :=
  inputs_refuted_unsat expanded read (objectIds_nodup expanded.1 read) refuted

/-! Goal order: the k-th goal row and the k-th goal item carry the same declaration. -/

/-- The source view of an entry, as `Bytes.source` builds it. -/
def entryDeclaration (value : Bytes.Entry) : Roles.Declaration Name FullFof.Formula :=
  ⟨value.original.name, value.role, value.original.body.formula⟩

theorem splits_items {α : Type} : ∀ values : List α, (splits values).map (fun split => split.2.1) = values
  | [] => rfl
  | head :: tail => by
    simp only [splits, List.map_cons, List.map_map]
    exact congrArg (List.cons head) (splits_items tail)

/-- The goal rows in order, as their declarations, are the goal items' entries in order. -/
theorem goal_rows_items {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    (read : readSigned (entriesOf bundle items) = some input) :
    ((splits input.rows).filter (fun split => decide (split.2.1.role = .conjecture))).map
        (fun split => split.2.1.declaration) =
      (goalItems bundle items).map (fun pair => entryDeclaration pair.2) := by
  obtain ⟨_, _, _, sources⟩ := readSigned_exact read
  have rows : ((splits input.rows).filter (fun split => decide (split.2.1.role = .conjecture))).map
      (fun split => split.2.1) = input.rows.filter (fun row => decide (row.role = .conjecture)) := by
    have commuted := List.filter_map (p := fun row : RoleRow => decide (row.role = .conjecture))
      (f := fun split : List RoleRow × RoleRow × List RoleRow => split.2.1) (l := splits input.rows)
    rw [splits_items] at commuted
    exact commuted.symm
  have entries : (goalItems bundle items).map (fun pair => entryDeclaration pair.2) =
      ((entriesOf bundle items).filter fun value => decide (value.role = .conjecture)).map entryDeclaration := by
    rw [← goalItems_entries, List.map_map]
    rfl
  have declarations : (input.rows.filter (fun row => decide (row.role = .conjecture))).map RoleRow.declaration =
      ((entriesOf bundle items).filter fun value => decide (value.role = .conjecture)).map entryDeclaration := by
    have mapped := congrArg (List.filter (fun declaration : Roles.Declaration Name FullFof.Formula =>
      decide (declaration.role = .conjecture))) sources
    rw [List.filter_map, Bytes.source, List.filter_map] at mapped
    exact mapped
  rw [entries, ← declarations, ← rows, List.map_map]
  rfl

/-- The per-item statement from a refuted task of that goal: the goal at index `index` among all conjectures is the item at the same index of `goalItems`. -/
theorem goal_item_entailed {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    {index : Nat} {before after : List RoleRow} {goal : RoleRow} {item : Coverage.Item}
    {entry : Bytes.Entry} {task : List SignedNumeric}
    (expanded : Expanded files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (selected : ((splits input.rows).filter (fun split => decide (split.2.1.role = .conjecture)))[index]? =
      some (before, goal, after))
    (identity : (goalItems bundle items)[index]? = some (item, entry))
    (built : goalTask before goal after = some task)
    (refuted : ¬ TaskSatisfiable input (task ++ distinctItems input bundle items)) :
    BundleGoalEntailed files maximum fuel item := by
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

#print axioms Fang.TptpCandidate.Roles.Bundle.eraseDups_loop_nodup
#print axioms Fang.TptpCandidate.Roles.Bundle.objectsOf_nodup
#print axioms Fang.TptpCandidate.Roles.Bundle.objectIds_nodup
#print axioms Fang.TptpCandidate.Roles.Bundle.goal_entailed_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.inputs_unsat_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.splits_items
#print axioms Fang.TptpCandidate.Roles.Bundle.goal_rows_items
#print axioms Fang.TptpCandidate.Roles.Bundle.goal_item_entailed

end Fang.TptpCandidate.Roles.Bundle
