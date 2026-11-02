/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent ordered-list consequence used by the actual-code composition. -/
import Equality

namespace FangParamodulation

theorem focus_split {α : Type} (values : List α) (index : Nat) (selected : α)
    (found : values[index]? = some selected) :
    ∃ before after, values = before ++ selected :: after ∧
      values.eraseIdx index = before ++ after ∧
      ∀ replacement, values.set index replacement = before ++ replacement :: after := by
  induction values generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      have same : head = selected := Option.some.inj found
      subst head
      exact ⟨[], tail, rfl, rfl, fun _ => rfl⟩
    | succ index =>
      obtain ⟨before, after, original, erased, replaced⟩ := ih index found
      refine ⟨head :: before, after, ?_, ?_, ?_⟩
      · simpa only [List.cons_append] using congrArg (List.cons head) original
      · change head :: tail.eraseIdx index = _
        rw [erased]
        rfl
      · intro replacement
        change head :: tail.set index replacement = _
        rw [replaced]
        rfl

/-- Removing one source pivot and replacing one target position is a logical
    consequence whenever those two selected values justify the replacement.
    Unselected values retain their positions and multiplicities. -/
theorem ordered_update_consequence {α : Type} (holds : α → Prop)
    (source target : List α) (sourceIndex targetIndex : Nat)
    (pivot selected replacement : α)
    (sourceAt : source[sourceIndex]? = some pivot)
    (targetAt : target[targetIndex]? = some selected)
    (sourceHolds : ∃ value ∈ source, holds value)
    (targetHolds : ∃ value ∈ target, holds value)
    (replaceHolds : holds pivot → holds selected → holds replacement) :
    ∃ value ∈ source.eraseIdx sourceIndex ++ target.set targetIndex replacement, holds value := by
  obtain ⟨sourceBefore, sourceAfter, sourceEq, erased, _⟩ := focus_split source sourceIndex pivot sourceAt
  obtain ⟨targetBefore, targetAfter, targetEq, _, replaced⟩ := focus_split target targetIndex selected targetAt
  rw [erased, replaced]
  obtain ⟨sourceValue, sourceMember, sourceTruth⟩ := sourceHolds
  rw [sourceEq] at sourceMember
  rcases List.mem_append.mp sourceMember with beforeMember | selectedOrAfter
  · exact ⟨sourceValue, List.mem_append_left _ (List.mem_append_left _ beforeMember), sourceTruth⟩
  · rcases List.mem_cons.mp selectedOrAfter with same | afterMember
    · subst sourceValue
      obtain ⟨targetValue, targetMember, targetTruth⟩ := targetHolds
      rw [targetEq] at targetMember
      rcases List.mem_append.mp targetMember with beforeMember | selectedOrAfter
      · exact ⟨targetValue, List.mem_append_right _ (List.mem_append_left _ beforeMember), targetTruth⟩
      · rcases List.mem_cons.mp selectedOrAfter with same | afterMember
        · subst targetValue
          exact ⟨replacement, List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self ..)),
            replaceHolds sourceTruth targetTruth⟩
        · exact ⟨targetValue, List.mem_append_right _
            (List.mem_append_right _ (List.mem_cons_of_mem _ afterMember)), targetTruth⟩
    · exact ⟨sourceValue, List.mem_append_left _ (List.mem_append_right _ afterMember), sourceTruth⟩

end FangParamodulation
