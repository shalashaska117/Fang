/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import DerivedState

namespace Fang.TstpExport.BuilderProof

def DerivedResult (problem : NamedProblem) (node : Nat)
    (result : ForInStep CollectorState) : Prop :=
  ∃ after, result = .yield after ∧ RowInvariant problem (node + 1) after

theorem process_derives (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause)
    (step : Step) (node : Nat) (state : CollectorState) (result : ForInStep CollectorState)
    (lower : LowerNames problem.names) (unique : problem.names.Nodup)
    (valid : StateInvariant problem clauses state) (rowsValid : RowInvariant problem node state)
    (trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses)
    (stepAt : certificate.steps[node]? = some step)
    (success : process problem certificate clauses (step, node) state = .ok result) :
    DerivedResult problem node result := by
  rcases state with ⟨rows, labels, emitted⟩
  by_cases needed : node ∈ ancestors certificate
  · cases clauseAt : clauses[node]? with
    | none => simp [process, needed, clauseAt, bind, Except.bind, throw] at success
    | some clause =>
      have checked := checked_trace_at _ certificate clauses trace node step clause stepAt clauseAt
      cases step with
      | input source =>
        cases rawAt : problem.signature.problem[source]? with
        | none => simp [process, needed, clauseAt, rawAt, bind, Except.bind, throw] at success
        | some raw =>
          cases nameAt : problem.names[source]? with
          | none => simp [process, needed, clauseAt, rawAt, nameAt, bind, Except.bind, throw] at success
          | some name =>
            by_cases seen : source ∈ emitted
            · obtain ⟨storedRaw, storedName, storedAt, storedNameAt, parent⟩ := valid.2 source seen
              have rawEq : storedRaw = raw := Option.some.inj (storedAt.symm.trans rawAt)
              have nameEq : storedName = name := Option.some.inj (storedNameAt.symm.trans nameAt)
              subst storedRaw
              subst storedName
              by_cases equal : raw = clause
              · simp [process, needed, clauseAt, rawAt, nameAt, seen, equal, pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                exact row_invariant_mono problem node (node + 1) (rows, labels, emitted) rowsValid (by omega)
              · simp [process, needed, clauseAt, rawAt, nameAt, seen, equal, pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                exact row_invariant_generated problem node (rows, labels, emitted)
                  { name := internalName node, clause, origin := .deduplicate node source name } .step lower rowsValid rfl
                  (dedup_row_justified problem rows clauses node source name raw clause rawAt parent checked)
            · have base := row_invariant_input problem node (rows, labels, emitted) source name raw lower unique
                rowsValid rawAt nameAt seen
              by_cases equal : raw = clause
              · subst raw
                simp [process, needed, clauseAt, rawAt, nameAt, seen, pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                exact row_invariant_mono problem node (node + 1)
                  (rows ++ [{ name, clause, origin := .input source name }], labels, source :: emitted) base (by omega)
              · simp [process, needed, clauseAt, rawAt, nameAt, seen, equal, pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                have added := row_invariant_generated problem node
                  (rows ++ [{ name, clause := raw, origin := .input source name }], labels, source :: emitted)
                  { name := internalName node, clause, origin := .deduplicate node source name } .step lower base rfl
                  (dedup_row_justified problem _ clauses node source name raw clause rawAt
                    ⟨{ name, clause := raw, origin := .input source name }, by simp, rfl, rfl⟩ checked)
                change RowInvariant problem (node + 1)
                  ((rows ++ [{ name, clause := raw, origin := .input source name }]) ++
                    [{ name := internalName node, clause, origin := .deduplicate node source name }],
                    labels, source :: emitted) at added
                rw [List.append_assoc] at added
                exact added
      | factor parent i j σ claimed =>
        cases labelAt : findLabel labels parent with
        | error reason => simp [process, needed, clauseAt, labelAt, bind, Except.bind] at success
        | ok name =>
          simp [process, needed, clauseAt, labelAt, bind, Except.bind, pure, Except.pure] at success
          refine ⟨_, success.symm, ?_⟩
          exact row_invariant_generated problem node (rows, labels, emitted)
            { name := internalName node, clause, origin := .factor node i j name σ } .step lower rowsValid rfl
            (factor_row_justified problem certificate clauses rows labels node parent i j name σ claimed clause
              trace stepAt clauseAt (stored_labels_match clauses (rows, labels, emitted) valid.1) labelAt)
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
                obtain ⟨leftJustified, rightJustified, resultJustified⟩ :=
                  resolution_rows_justified problem certificate clauses rows labels node left i right j
                    leftName rightName σ claimed clause lc rc trace stepAt clauseAt leftAt rightAt
                    (stored_labels_match clauses (rows, labels, emitted) valid.1) leftLabel rightLabel
                simpa [RowInvariant, NamesBefore, leftRow, rightRow, resolveRow, List.append_assoc] using
                  row_invariant_resolution problem node (rows, labels, emitted) leftName rightName lc rc clause i j σ
                    lower rowsValid leftJustified rightJustified resultJustified
  · simp [process, needed, pure, Except.pure] at success
    exact ⟨_, success.symm, row_invariant_mono problem node (node + 1) _ rowsValid (by omega)⟩

end Fang.TstpExport.BuilderProof
