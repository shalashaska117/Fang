/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Rows

namespace Fang.TstpExport

theorem checked_suffix (problem : Problem) (steps : List Step) (before after : List Clause)
    (h : checkSteps problem before steps = some after) :
    ∃ suffix, after = before ++ suffix ∧ suffix.length = steps.length := by
  induction steps generalizing before after with
  | nil =>
    have same : before = after := Option.some.inj h
    subst after
    exact ⟨[], by simp, rfl⟩
  | cons step rest ih =>
    cases hs : checkStep problem before step with
    | none => simp [checkSteps, hs] at h
    | some clause =>
      simp only [checkSteps, hs, bind, Option.bind] at h
      obtain ⟨suffix, result, size⟩ := ih (before ++ [clause]) after h
      refine ⟨clause :: suffix, ?_, by simp [size]⟩
      simpa only [List.append_assoc, List.singleton_append] using result

private theorem lookup_append {α : Type} (before extra : List α) (index : Nat) (value : α)
    (h : before[index]? = some value) : (before ++ extra)[index]? = some value := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).choose]
  exact h

theorem checkStep_append (problem : Problem) (before extra : List Clause)
    (step : Step) (result : Clause) (h : checkStep problem before step = some result) :
    checkStep problem (before ++ extra) step = some result := by
  cases step with
  | input i => exact h
  | factor parent i j σ claimed =>
    cases hp : before[parent]? with
    | none => simp [checkStep, hp] at h
    | some clause =>
      have extended := lookup_append before extra parent clause hp
      simpa only [checkStep, hp, extended, bind, Option.bind] using h
  | resolve left i right j σ claimed =>
    cases hl : before[left]? with
    | none => simp [checkStep, hl] at h
    | some lc =>
      cases hr : before[right]? with
      | none => simp [checkStep, hl, hr] at h
      | some rc =>
        have leftExtended := lookup_append before extra left lc hl
        have rightExtended := lookup_append before extra right rc hr
        simpa only [checkStep, hl, hr, leftExtended, rightExtended, bind, Option.bind] using h

/-- Every position in a successful trace has the same checked inference when
    read against the final clause vector used by the actual exporter. -/
theorem checked_trace (problem : Problem) (steps : List Step) (before after : List Clause)
    (h : checkSteps problem before steps = some after) :
    ∀ index step, steps[index]? = some step →
      ∃ clause, after[before.length + index]? = some clause ∧
        checkStep problem after step = some clause := by
  induction steps generalizing before after with
  | nil => intro index step member; simp at member
  | cons first rest ih =>
    cases hf : checkStep problem before first with
    | none => simp [checkSteps, hf] at h
    | some firstClause =>
      simp only [checkSteps, hf, bind, Option.bind] at h
      intro index step member
      cases index with
      | zero =>
        have same : first = step := Option.some.inj member
        subst step
        obtain ⟨suffix, result, _⟩ := checked_suffix problem rest (before ++ [firstClause]) after h
        have result' : after = before ++ (firstClause :: suffix) := by
          simpa only [List.append_assoc, List.singleton_append] using result
        refine ⟨firstClause, ?_, ?_⟩
        · rw [result']
          simp
        · rw [result']
          exact checkStep_append problem before (firstClause :: suffix) first firstClause hf
      | succ index =>
        have tailMember : rest[index]? = some step := member
        obtain ⟨clause, position, checked⟩ := ih (before ++ [firstClause]) after h index step tailMember
        exact ⟨clause, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using position, checked⟩

theorem checked_trace_at (problem : Problem) (certificate : Certificate) (clauses : List Clause)
    (h : checkSteps problem [] certificate.steps = some clauses)
    (index : Nat) (step : Step) (clause : Clause)
    (stepAt : certificate.steps[index]? = some step) (clauseAt : clauses[index]? = some clause) :
    checkStep problem clauses step = some clause := by
  obtain ⟨found, position, checked⟩ := checked_trace problem certificate.steps [] clauses h index step stepAt
  have same : found = clause := Option.some.inj (position.symm.trans (by simpa using clauseAt))
  simpa only [same] using checked

end Fang.TstpExport
