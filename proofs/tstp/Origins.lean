/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Derivation

namespace Fang.TstpExport.BuilderProof

/-- Numeric provenance of each actual row. Membership in `ancestors` refers to
    the executable pruning set; exact graph reachability is a separate claim. -/
def CertificateRow (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (row : Row) : Prop :=
  match row.origin with
  | .input source name => ∃ node, node ∈ ancestors certificate ∧
      certificate.steps[node]? = some (.input source) ∧
      problem.names[source]? = some name ∧ row.name = name ∧
      problem.signature.problem[source]? = some row.clause
  | .deduplicate node source parent => node ∈ ancestors certificate ∧
      certificate.steps[node]? = some (.input source) ∧ clauses[node]? = some row.clause ∧
      problem.names[source]? = some parent ∧ row.name = internalName node
  | .rename node right _ => node ∈ ancestors certificate ∧
      ∃ left i rightNode j σ claimed source,
        certificate.steps[node]? = some (.resolve left i rightNode j σ claimed) ∧
        clauses[if right then rightNode else left]? = some source ∧
        row.clause = source.map (Literal.rename (if right then rightRename else leftRename)) ∧
        row.name = generatedName (if right then .right else .left) node
  | .factor node i j _ σ => node ∈ ancestors certificate ∧
      ∃ parent claimed, certificate.steps[node]? = some (.factor parent i j σ claimed) ∧
        clauses[node]? = some row.clause ∧ row.name = internalName node
  | .resolve node i j leftName rightName σ => node ∈ ancestors certificate ∧
      ∃ left right claimed, certificate.steps[node]? = some (.resolve left i right j σ claimed) ∧
        clauses[node]? = some row.clause ∧ row.name = internalName node ∧
        leftName = generatedName .left node ∧ rightName = generatedName .right node

def CertificateRows (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (rows : List Row) : Prop :=
  ∀ row ∈ rows, CertificateRow problem certificate clauses row

theorem certificate_rows_append (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (rows : List Row) (row : Row)
    (prior : CertificateRows problem certificate clauses rows)
    (added : CertificateRow problem certificate clauses row) :
    CertificateRows problem certificate clauses (rows ++ [row]) := by
  intro current member
  rcases List.mem_append.mp member with earlier | last
  · exact prior current earlier
  · simpa only [List.mem_singleton.mp last] using added

def OriginResult (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (result : ForInStep CollectorState) : Prop :=
  ∃ after, result = .yield after ∧ CertificateRows problem certificate clauses after.1

theorem process_origins (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause)
    (step : Step) (node : Nat) (state : CollectorState) (result : ForInStep CollectorState)
    (prior : CertificateRows problem certificate clauses state.1)
    (stepAt : certificate.steps[node]? = some step)
    (success : process problem certificate clauses (step, node) state = .ok result) :
    OriginResult problem certificate clauses result := by
  rcases state with ⟨rows, labels, emitted⟩
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
            have rawOrigin : CertificateRow problem certificate clauses
                { name, clause := raw, origin := .input source name } :=
              ⟨node, needed, stepAt, nameAt, rfl, rawAt⟩
            have dedupOrigin : CertificateRow problem certificate clauses
                { name := internalName node, clause, origin := .deduplicate node source name } :=
              ⟨needed, stepAt, clauseAt, nameAt, rfl⟩
            by_cases seen : source ∈ emitted
            · by_cases equal : raw = clause
              · simp [process, needed, clauseAt, rawAt, nameAt, seen, equal, pure, Except.pure] at success
                exact ⟨_, success.symm, prior⟩
              · simp [process, needed, clauseAt, rawAt, nameAt, seen, equal, pure, Except.pure] at success
                exact ⟨_, success.symm, certificate_rows_append _ _ _ _ _ prior dedupOrigin⟩
            · have withRaw := certificate_rows_append _ _ _ _ _ prior rawOrigin
              by_cases equal : raw = clause
              · subst raw
                simp [process, needed, clauseAt, rawAt, nameAt, seen, pure, Except.pure] at success
                exact ⟨_, success.symm, withRaw⟩
              · simp [process, needed, clauseAt, rawAt, nameAt, seen, equal, pure, Except.pure] at success
                refine ⟨_, success.symm, ?_⟩
                simpa only [List.append_assoc, List.singleton_append] using
                  certificate_rows_append _ _ _ _ _ withRaw dedupOrigin
      | factor parent i j σ claimed =>
        cases labelAt : findLabel labels parent with
        | error reason => simp [process, needed, clauseAt, labelAt, bind, Except.bind] at success
        | ok name =>
          simp [process, needed, clauseAt, labelAt, bind, Except.bind, pure, Except.pure] at success
          refine ⟨_, success.symm, certificate_rows_append _ _ _ _ _ prior ?_⟩
          exact ⟨needed, parent, claimed, stepAt, clauseAt, rfl⟩
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
                have leftOrigin : CertificateRow problem certificate clauses (leftRow node leftName lc) :=
                  ⟨needed, left, i, right, j, σ, claimed, lc, stepAt, leftAt, rfl, rfl⟩
                have rightOrigin : CertificateRow problem certificate clauses (rightRow node rightName rc) :=
                  ⟨needed, left, i, right, j, σ, claimed, rc, stepAt, rightAt, rfl, rfl⟩
                have resultOrigin : CertificateRow problem certificate clauses (resolveRow node i j σ clause) :=
                  ⟨needed, left, right, claimed, stepAt, clauseAt, rfl, rfl, rfl⟩
                have first := certificate_rows_append _ _ _ _ _ prior leftOrigin
                have second := certificate_rows_append _ _ _ _ _ first rightOrigin
                have third := certificate_rows_append _ _ _ _ _ second resultOrigin
                simpa [leftRow, rightRow, resolveRow, List.append_assoc] using third
  · simp [process, needed, pure, Except.pure] at success
    exact ⟨_, success.symm, prior⟩

theorem forIn_origins (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause)
    (entries : List (Step × Nat)) (before after : CollectorState)
    (positions : ∀ entry ∈ entries, certificate.steps[entry.2]? = some entry.1)
    (prior : CertificateRows problem certificate clauses before.1)
    (success : forIn entries before (process problem certificate clauses) = .ok after) :
    CertificateRows problem certificate clauses after.1 := by
  induction entries generalizing before with
  | nil =>
    have same : before = after := by simpa [pure, Except.pure] using success
    simpa [same] using prior
  | cons entry entries ih =>
    cases stepped : process problem certificate clauses entry before with
    | error reason => simp [List.forIn_cons, stepped, bind, Except.bind] at success
    | ok result =>
      obtain ⟨middle, yieldEq, origins⟩ := process_origins problem certificate clauses entry.1 entry.2 before result
        prior (positions entry (by simp)) stepped
      subst result
      apply ih middle (fun entry member => positions entry (List.mem_cons_of_mem _ member)) origins
      simpa [List.forIn_cons, stepped, bind, Except.bind] using success

theorem runCollector_origins (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (state : CollectorState)
    (success : runCollector problem certificate clauses = .ok state) :
    CertificateRows problem certificate clauses state.1 := by
  apply forIn_origins problem certificate clauses certificate.steps.zipIdx ([], [], []) state _ (by simp [CertificateRows]) success
  intro entry member
  obtain ⟨index, indexed⟩ := List.mem_iff_getElem?.mp member
  have lookup := List.getElem?_zipIdx (l := certificate.steps) (i := 0) (j := index)
  rw [indexed] at lookup
  cases stepAt : certificate.steps[index]? with
  | none => simp [stepAt] at lookup
  | some step =>
    have pair : entry = (step, index) := by simpa [stepAt] using lookup
    simpa [pair] using stepAt

theorem build_origins (problem : NamedProblem) (certificate : Certificate) (output : Export)
    (success : build problem certificate = .ok output) :
    ∃ clauses, checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses ∧
      CertificateRows problem certificate clauses output.rows := by
  obtain ⟨clauses, rows, labels, trace, collected, finished⟩ := build_collects success
  refine ⟨clauses, trace, ?_⟩
  rw [finish_rows problem certificate rows labels output finished]
  simp only [collect, collectWith_eq_run] at collected
  cases ran : runCollector problem certificate clauses with
  | error reason => simp [ran, bind, Except.bind] at collected
  | ok state =>
    have pair : (state.1, state.2.1) = (rows, labels) := by
      simpa [ran, bind, Except.bind, pure, Except.pure] using collected
    have origins := runCollector_origins problem certificate clauses state ran
    rcases Prod.mk.inj pair with ⟨rowEq, _⟩
    simpa [rowEq] using origins

end Fang.TstpExport.BuilderProof
