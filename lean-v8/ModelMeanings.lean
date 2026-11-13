/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The positive signed meanings, next to the refuted ones of `RoleMeaningLimit` and over the same frame parameter,
   expansion, separation of distinct objects and sentence semantics. `ByteInputsSatisfiable` is the
   frame-parametric form of `ByteBundleInputsSatisfiable` (`BundleRoles.lean`); `GoalCountermodel` is a model of the
   selected premises in which one selected conjecture, identified by its bundle item, is false. Each contradicts
   the meaning its path refutes. -/
import RoleMeaningLimit

namespace Fang.TptpCandidate.Roles.Bundle.V3
open FullFof

/-- The statement for SZS Satisfiable on the signed path: no selected conjecture, and the positive inputs have a model
    that keeps distinct objects apart. -/
def ByteInputsSatisfiable (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, Expanded frame files maximum fuel bundle items ∧ goalItems bundle items = [] ∧
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items) ∧
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.positiveInputs (Bytes.source (entriesOf bundle items))) model

/-- One selected original conjecture, identified by its bundle item, is false in a model of the selected premises
    that keeps distinct objects apart. -/
def GoalCountermodel (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat)
    (item : Coverage.Item) : Prop :=
  ∃ bundle items entry, Expanded frame files maximum fuel bundle items ∧ (item, entry) ∈ goalItems bundle items ∧
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf bundle items) ∧
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model ∧
      ¬ Bytes.sentence model entry.original.body.formula

/-- The statement for SZS CounterSatisfiable: some selected conjecture has a countermodel. -/
def ByteCounterSatisfiable (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ item, GoalCountermodel frame files maximum fuel item

theorem inputsSatisfiable_not_unsatisfiable {frame : Frame} {files : List (Coverage.Key × List UInt8)}
    {maximum fuel : Nat} (satisfiable : ByteInputsSatisfiable frame files maximum fuel) :
    ¬ ByteUnsatisfiable frame files maximum fuel := by
  rintro ⟨bundle, items, expanded, _, refuted⟩
  obtain ⟨other, others, otherExpanded, _, D, inhabited, model, separated, holds⟩ := satisfiable
  obtain ⟨rfl, rfl⟩ := expanded_unique expanded otherExpanded
  exact refuted D inhabited model separated holds

theorem countermodel_not_entailed {frame : Frame} {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {item : Coverage.Item} (countermodel : GoalCountermodel frame files maximum fuel item) :
    ¬ GoalEntailed frame files maximum fuel item := by
  rintro ⟨bundle, items, entry, expanded, member, entails⟩
  obtain ⟨other, others, otherEntry, otherExpanded, otherMember, D, inhabited, model, separated, premises, fails⟩ :=
    countermodel
  obtain ⟨rfl, rfl⟩ := expanded_unique expanded otherExpanded
  have first := V2.goalItems_entry member
  have second := V2.goalItems_entry otherMember
  rw [first] at second
  simp only [Option.some.injEq, RoleStatement.formula.injEq] at second
  subst second
  exact fails (entails D inhabited model separated premises)

theorem counterSatisfiable_not_theorem {frame : Frame} {files : List (Coverage.Key × List UInt8)}
    {maximum fuel : Nat} (countermodel : ByteCounterSatisfiable frame files maximum fuel) :
    ¬ ByteTheorem frame files maximum fuel := by
  rintro ⟨bundle, items, expanded, _, entailed⟩
  obtain ⟨item, other, others, entry, otherExpanded, member, D, inhabited, model, separated, premises, fails⟩ :=
    countermodel
  obtain ⟨rfl, rfl⟩ := expanded_unique expanded otherExpanded
  exact fails (entailed (item, entry) member D inhabited model separated premises)

end Fang.TptpCandidate.Roles.Bundle.V3
