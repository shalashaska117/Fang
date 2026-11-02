/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Adapted from proofs/tstp/Derivation.lean. DisjointNames replaces the stronger
   source-identifier premise. All executable builder definitions and the old
   finish_rows theorem are reused. This isolated candidate is unchecked. -/
import Fang.FOF.TSTP.DisjointProcess

namespace Fang.TstpExport.BuilderProof

theorem forIn_zipIdx_derives_disjoint (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause)
    (lower : DisjointNames problem.names) (unique : problem.names.Nodup)
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
        process_derives_disjoint problem certificate clauses step start before result lower unique valid rowsValid trace stepAt stepped
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

theorem runCollector_derives_disjoint (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (state : CollectorState)
    (lower : DisjointNames problem.names) (unique : problem.names.Nodup)
    (trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses)
    (success : runCollector problem certificate clauses = .ok state) :
    RowInvariant problem certificate.steps.length state := by
  simpa using forIn_zipIdx_derives_disjoint problem certificate clauses lower unique trace certificate.steps 0
    ([], [], []) state (by intro index step lookup; simpa using lookup)
    (state_empty problem clauses) (row_invariant_empty problem 0) success

theorem collect_derives_disjoint (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (rows : List Row) (labels : List (Nat × String))
    (lower : DisjointNames problem.names) (unique : problem.names.Nodup)
    (trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses)
    (success : collect problem certificate clauses = .ok (rows, labels)) :
    Derivation problem rows := by
  simp only [collect, collectWith_eq_run] at success
  cases ran : runCollector problem certificate clauses with
  | error reason => simp [ran, bind, Except.bind] at success
  | ok state =>
    have pair : (state.1, state.2.1) = (rows, labels) := by
      simpa [ran, bind, Except.bind, pure, Except.pure] using success
    have valid := (runCollector_derives_disjoint problem certificate clauses state lower unique trace ran).2
    rcases Prod.mk.inj pair with ⟨rowEq, _⟩
    simpa [rowEq] using valid

/-- Every returned row of the actual builder belongs to a fresh, justified
    derivation. This theorem is about typed rows, not printed text parsing. -/
theorem build_derivation_disjoint (problem : NamedProblem) (certificate : Certificate) (output : Export)
    (lower : DisjointNames problem.names) (unique : problem.names.Nodup)
    (success : build problem certificate = .ok output) : Derivation problem output.rows := by
  obtain ⟨clauses, rows, labels, trace, collected, finished⟩ := build_collects success
  rw [finish_rows problem certificate rows labels output finished]
  exact collect_derives_disjoint problem certificate clauses rows labels lower unique trace collected

theorem decoded_build_derivation_disjoint (input : String) (problem : NamedProblem)
    (certificate : Certificate) (output : Export)
    (decoded : decodeNamed input = .ok problem) (built : build problem certificate = .ok output) :
    Derivation problem output.rows := by
  have names := decoded_names input problem decoded
  exact build_derivation_disjoint problem certificate output (lower_names_disjoint names.2) names.1 built

end Fang.TstpExport.BuilderProof
