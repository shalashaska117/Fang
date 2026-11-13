/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Process

namespace Fang.TstpExport.BuilderProof

def ResultInvariant (problem : NamedProblem) (clauses : List Clause)
    (result : ForInStep CollectorState) : Prop :=
  ∃ after, result = .yield after ∧ StateInvariant problem clauses after

theorem process_preserves (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause)
    (entry : Step × Nat) (state : CollectorState) (result : ForInStep CollectorState)
    (valid : StateInvariant problem clauses state)
    (success : process problem certificate clauses entry state = .ok result) :
    ResultInvariant problem clauses result := by
  rcases state with ⟨rows, labels, emitted⟩
  rcases entry with ⟨step, node⟩
  by_cases needed : node ∈ ancestors certificate
  · cases clauseAt : clauses[node]? with
    | none => simp [process, needed, clauseAt, bind, Except.bind, throw] at success
    | some clause =>
      cases step with
      | input source =>
        cases rawAt : problem.signature.problem[source]? with
        | none => simp [process, needed, clauseAt, rawAt, bind, Except.bind, throw] at success
        | some raw =>
          cases nameAt : problem.names[source]? with
          | none => simp [process, needed, clauseAt, rawAt, nameAt, bind, Except.bind, throw] at success
          | some name =>
            by_cases seen : source ∈ emitted
            · obtain ⟨storedRaw, storedName, storedAt, storedNameAt, parent⟩ :=
                valid.2 source seen
              have rawEq : storedRaw = raw := Option.some.inj (storedAt.symm.trans rawAt)
              have nameEq : storedName = name := Option.some.inj (storedNameAt.symm.trans nameAt)
              subst storedRaw
              subst storedName
              by_cases equal : raw = clause
              · simp [process, needed, clauseAt, rawAt, nameAt, seen, equal,
                  pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                exact state_label problem clauses (rows, labels, emitted) node name clause valid clauseAt
                  (by simpa [equal] using parent)
              · simp [process, needed, clauseAt, rawAt, nameAt, seen, equal,
                  pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                exact state_emit_row problem clauses (rows, labels, emitted) node
                  { name := internalName node, clause, origin := .deduplicate node source name } valid clauseAt
            · have base := state_emit_input problem clauses (rows, labels, emitted) source name raw valid rawAt nameAt
              by_cases equal : raw = clause
              · subst raw
                simp [process, needed, clauseAt, rawAt, nameAt, seen, pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                exact state_label problem clauses
                  (rows ++ [{ name, clause, origin := .input source name }], labels, source :: emitted)
                  node name clause base clauseAt
                  ⟨{ name, clause, origin := .input source name }, by simp, rfl, rfl⟩
              · simp [process, needed, clauseAt, rawAt, nameAt, seen, equal,
                  pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                have added := state_emit_row problem clauses
                  (rows ++ [{ name, clause := raw, origin := .input source name }], labels, source :: emitted) node
                  { name := internalName node, clause, origin := .deduplicate node source name } base clauseAt
                change StateInvariant problem clauses
                  ((rows ++ [{ name, clause := raw, origin := .input source name }]) ++
                    [{ name := internalName node, clause, origin := .deduplicate node source name }],
                    (node, internalName node) :: labels, source :: emitted) at added
                rw [List.append_assoc] at added
                exact added
      | factor parent i j σ claimed =>
        cases labelAt : findLabel labels parent with
        | error reason => simp [process, needed, clauseAt, labelAt, bind, Except.bind] at success
        | ok name =>
          simp [process, needed, clauseAt, labelAt, bind, Except.bind, pure, Except.pure] at success
          refine ⟨_, success.symm, ?_⟩
          exact state_emit_row problem clauses (rows, labels, emitted) node
            { name := internalName node, clause, origin := .factor node i j name σ } valid clauseAt
      | resolve left i right j σ claimed =>
        cases leftAt : clauses[left]? with
        | none => simp [process, needed, clauseAt, leftAt, bind, Except.bind, throw] at success
        | some lc =>
          cases rightAt : clauses[right]? with
          | none => simp [process, needed, clauseAt, leftAt, rightAt, bind, Except.bind, throw] at success
          | some rc =>
            cases leftLabel : findLabel labels left with
            | error reason => simp [process, needed, clauseAt, leftAt, rightAt, leftLabel, bind, Except.bind] at success
            | ok leftName =>
              cases rightLabel : findLabel labels right with
              | error reason =>
                simp [process, needed, clauseAt, leftAt, rightAt, leftLabel, rightLabel, bind, Except.bind] at success
              | ok rightName =>
                simp [process, needed, clauseAt, leftAt, rightAt, leftLabel, rightLabel,
                  bind, Except.bind, pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                simpa [leftRow, rightRow, resolveRow, List.append_assoc] using
                  state_emit_row problem clauses
                    (rows ++ [leftRow node leftName lc, rightRow node rightName rc], labels, emitted) node
                    (resolveRow node i j σ clause)
                    (state_append problem clauses (rows, labels, emitted)
                      [leftRow node leftName lc, rightRow node rightName rc] valid) clauseAt
  · simp [process, needed, pure, Except.pure] at success
    exact ⟨_, success.symm, valid⟩

theorem forIn_preserves (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause)
    (entries : List (Step × Nat)) (before after : CollectorState)
    (valid : StateInvariant problem clauses before)
    (success : forIn entries before (process problem certificate clauses) = .ok after) :
    StateInvariant problem clauses after := by
  induction entries generalizing before with
  | nil =>
    have same : before = after := by simpa [pure, Except.pure] using success
    simpa [same] using valid
  | cons entry entries ih =>
    cases stepped : process problem certificate clauses entry before with
    | error reason => simp [List.forIn_cons, stepped, bind, Except.bind] at success
    | ok step =>
      obtain ⟨middle, same, middleValid⟩ := process_preserves problem certificate clauses entry before step valid stepped
      subst step
      apply ih middle middleValid
      simpa [List.forIn_cons, stepped, bind, Except.bind] using success

theorem runCollector_invariant (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (state : CollectorState)
    (success : runCollector problem certificate clauses = .ok state) :
    StateInvariant problem clauses state :=
  forIn_preserves problem certificate clauses certificate.steps.zipIdx ([], [], []) state
    (state_empty problem clauses) success

theorem collect_labels_match (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (rows : List Row) (labels : List (Nat × String))
    (success : collect problem certificate clauses = .ok (rows, labels)) :
    LabelsMatch clauses rows labels := by
  simp only [collect, collectWith_eq_run] at success
  cases ran : runCollector problem certificate clauses with
  | error reason => simp [ran, bind, Except.bind] at success
  | ok state =>
    have pair : (state.1, state.2.1) = (rows, labels) := by
      simpa [ran, bind, Except.bind, pure, Except.pure] using success
    have valid := stored_labels_match clauses state (runCollector_invariant problem certificate clauses state ran).1
    rcases Prod.mk.inj pair with ⟨rowEq, labelEq⟩
    simpa [rowEq, labelEq] using valid

end Fang.TstpExport.BuilderProof
