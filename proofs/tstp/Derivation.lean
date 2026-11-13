/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import DerivedProcess

namespace Fang.TstpExport.BuilderProof

theorem forIn_zipIdx_derives (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause)
    (lower : LowerNames problem.names) (unique : problem.names.Nodup)
    (trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses)
    (remaining : List Step) (start : Nat) (before after : CollectorState)
    (positions : ∀ index step, remaining[index]? = some step → certificate.steps[start + index]? = some step)
    (valid : StateInvariant problem clauses before) (rowsValid : RowInvariant problem start before)
    (success : forIn (remaining.zipIdx start) before (process problem certificate clauses) = .ok after) :
    RowInvariant problem (start + remaining.length) after := by
  induction remaining generalizing start before with
  | nil =>
    have same : before = after := by simpa [pure, Except.pure] using success
    simpa [same] using rowsValid
  | cons step remaining ih =>
    have stepAt : certificate.steps[start]? = some step := by
      simpa using positions 0 step (by simp)
    cases stepped : process problem certificate clauses (step, start) before with
    | error reason => simp [List.forIn_cons, stepped, bind, Except.bind] at success
    | ok result =>
      obtain ⟨middle, yieldEq, middleRows⟩ :=
        process_derives problem certificate clauses step start before result lower unique valid rowsValid trace stepAt stepped
      subst result
      have middleValid : StateInvariant problem clauses middle := by
        obtain ⟨stored, same, invariant⟩ :=
          process_preserves problem certificate clauses (step, start) before (.yield middle) valid stepped
        cases same
        exact invariant
      have nextPositions : ∀ index other, remaining[index]? = some other →
          certificate.steps[(start + 1) + index]? = some other := by
        intro index other lookup
        have found := positions (index + 1) other (by simpa using lookup)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found
      have remainingRun : forIn (remaining.zipIdx (start + 1)) middle
          (process problem certificate clauses) = .ok after := by
        simpa [List.forIn_cons, stepped, bind, Except.bind] using success
      have final := ih (start + 1) middle nextPositions middleValid middleRows remainingRun
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final

theorem runCollector_derives (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (state : CollectorState)
    (lower : LowerNames problem.names) (unique : problem.names.Nodup)
    (trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses)
    (success : runCollector problem certificate clauses = .ok state) :
    RowInvariant problem certificate.steps.length state := by
  simpa using forIn_zipIdx_derives problem certificate clauses lower unique trace certificate.steps 0
    ([], [], []) state (by intro index step lookup; simpa using lookup)
    (state_empty problem clauses) (row_invariant_empty problem 0) success

theorem collect_derives (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (rows : List Row) (labels : List (Nat × String))
    (lower : LowerNames problem.names) (unique : problem.names.Nodup)
    (trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses)
    (success : collect problem certificate clauses = .ok (rows, labels)) :
    Derivation problem rows := by
  simp only [collect, collectWith_eq_run] at success
  cases ran : runCollector problem certificate clauses with
  | error reason => simp [ran, bind, Except.bind] at success
  | ok state =>
    have pair : (state.1, state.2.1) = (rows, labels) := by
      simpa [ran, bind, Except.bind, pure, Except.pure] using success
    have valid := (runCollector_derives problem certificate clauses state lower unique trace ran).2
    rcases Prod.mk.inj pair with ⟨rowEq, _⟩
    simpa [rowEq] using valid

theorem finish_rows (problem : NamedProblem) (certificate : Certificate)
    (rows : List Row) (labels : List (Nat × String)) (output : Export)
    (success : finish problem certificate rows labels = .ok output) : output.rows = rows := by
  cases finalAt : findLabel labels certificate.final with
  | error reason => simp [finish, finalAt, bind, Except.bind] at success
  | ok finalName =>
    simp only [finish, finalAt, bind, Except.bind] at success
    split at success
    · simp [throw, throwThe] at success
    · split at success
      · simp [throw, throwThe] at success
      · have same : ({ signature := problem, rows, finalName } : Export) = output := by
          simpa [pure, Except.pure] using success
        cases same
        rfl

/-- Every returned row of the actual builder belongs to a fresh, justified
    derivation. This theorem is about typed rows, not printed text parsing. -/
theorem build_derivation (problem : NamedProblem) (certificate : Certificate) (output : Export)
    (lower : LowerNames problem.names) (unique : problem.names.Nodup)
    (success : build problem certificate = .ok output) : Derivation problem output.rows := by
  obtain ⟨clauses, rows, labels, trace, collected, finished⟩ := build_collects success
  rw [finish_rows problem certificate rows labels output finished]
  exact collect_derives problem certificate clauses rows labels lower unique trace collected

theorem decoded_build_derivation (input : String) (problem : NamedProblem)
    (certificate : Certificate) (output : Export)
    (decoded : decodeNamed input = .ok problem) (built : build problem certificate = .ok output) :
    Derivation problem output.rows := by
  have names := decoded_names input problem decoded
  exact build_derivation problem certificate output names.2 names.1 built

end Fang.TstpExport.BuilderProof
