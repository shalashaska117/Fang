/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Witness

namespace Fang.TstpExport.BuilderProof

abbrev CollectorState := List Row × List (Nat × String) × List Nat

/-- The actual loop body, with its mutable state exposed for induction. -/
def process (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause)
    (entry : Step × Nat) (state : CollectorState) : Except String (ForInStep CollectorState) := do
  let (step, index) := entry
  let needed := ancestors certificate
  let mut rows := state.1
  let mut labels := state.2.1
  let mut emittedInputs := state.2.2
  if needed.contains index then
    let some clause := clauses[index]? | throw "export-error: missing checked clause"
    match step with
    | .input sourceIndex =>
      let some raw := problem.signature.problem[sourceIndex]?
        | throw "export-error: input index out of range"
      let some sourceName := problem.names[sourceIndex]?
        | throw "export-error: missing input name"
      if !emittedInputs.contains sourceIndex then
        rows := rows ++ [{ name := sourceName, clause := raw, origin := .input sourceIndex sourceName }]
        emittedInputs := sourceIndex :: emittedInputs
      if raw = clause then
        labels := (index, sourceName) :: labels
      else
        let name := internalName index
        rows := rows ++ [{ name, clause, origin := .deduplicate index sourceIndex sourceName }]
        labels := (index, name) :: labels
    | .factor parent first second substitution _ =>
      let parent ← findLabel labels parent
      let name := internalName index
      rows := rows ++ [{ name, clause, origin := .factor index first second parent substitution }]
      labels := (index, name) :: labels
    | .resolve left leftPos right rightPos substitution _ =>
      let some leftClause := clauses[left]? | throw "export-error: left clause unavailable"
      let some rightClause := clauses[right]? | throw "export-error: right clause unavailable"
      let leftParent ← findLabel labels left
      let rightParent ← findLabel labels right
      let left := s!"fang:left:{index}"
      let right := s!"fang:right:{index}"
      rows := rows ++ [
        { name := left, clause := leftClause.map (Literal.rename leftRename), origin := .rename index false leftParent },
        { name := right, clause := rightClause.map (Literal.rename rightRename), origin := .rename index true rightParent }]
      let name := internalName index
      rows := rows ++ [{ name, clause, origin := .resolve index leftPos rightPos left right substitution }]
      labels := (index, name) :: labels
  pure (.yield (rows, labels, emittedInputs))

def runCollector (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause) :
    Except String CollectorState :=
  forIn certificate.steps.zipIdx ([], [], []) (process problem certificate clauses)

theorem collectWith_eq_run {α : Type} (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (next : List Row → List (Nat × String) → Except String α) :
    collectWith problem certificate clauses next =
      (do let state ← runCollector problem certificate clauses; next state.1 state.2.1) := by
  rfl

def StoredLabels (clauses : List Clause) (state : CollectorState) : Prop :=
  ∀ node name, (node, name) ∈ state.2.1 →
    ∃ clause, clauses[node]? = some clause ∧ Parent state.1 name clause

def EmittedInputs (problem : NamedProblem) (state : CollectorState) : Prop :=
  ∀ source, source ∈ state.2.2 → ∃ raw name,
    problem.signature.problem[source]? = some raw ∧ problem.names[source]? = some name ∧
      Parent state.1 name raw

def StateInvariant (problem : NamedProblem) (clauses : List Clause) (state : CollectorState) : Prop :=
  StoredLabels clauses state ∧ EmittedInputs problem state

theorem findLabel_member (labels : List (Nat × String)) (node : Nat) (name : String)
    (success : findLabel labels node = .ok name) : (node, name) ∈ labels := by
  cases found : labels.find? (fun entry => entry.1 == node) with
  | none => simp [findLabel, found] at success
  | some entry =>
    have member := List.mem_of_find?_eq_some found
    have matching := List.find?_some found
    have label : entry.2 = name := by simpa [findLabel, found] using success
    have index : entry.1 = node := by simpa using matching
    have pair : entry = (node, name) := Prod.ext index label
    simpa only [pair] using member

theorem stored_labels_match (clauses : List Clause) (state : CollectorState)
    (stored : StoredLabels clauses state) : LabelsMatch clauses state.1 state.2.1 := by
  intro node name success
  exact stored node name (findLabel_member state.2.1 node name success)

theorem state_empty (problem : NamedProblem) (clauses : List Clause) :
    StateInvariant problem clauses ([], [], []) := by
  simp [StateInvariant, StoredLabels, EmittedInputs]

theorem state_append (problem : NamedProblem) (clauses : List Clause) (state : CollectorState)
    (extra : List Row) (valid : StateInvariant problem clauses state) :
    StateInvariant problem clauses (state.1 ++ extra, state.2.1, state.2.2) := by
  constructor
  · intro node name member
    obtain ⟨clause, clauseAt, parent⟩ := valid.1 node name member
    exact ⟨clause, clauseAt, parent_append _ extra _ _ parent⟩
  · intro source member
    obtain ⟨raw, name, rawAt, nameAt, parent⟩ := valid.2 source member
    exact ⟨raw, name, rawAt, nameAt, parent_append _ extra _ _ parent⟩

theorem state_label (problem : NamedProblem) (clauses : List Clause) (state : CollectorState)
    (node : Nat) (name : String) (clause : Clause)
    (valid : StateInvariant problem clauses state) (clauseAt : clauses[node]? = some clause)
    (parent : Parent state.1 name clause) :
    StateInvariant problem clauses (state.1, (node, name) :: state.2.1, state.2.2) := by
  constructor
  · intro other otherName member
    rcases List.mem_cons.mp member with same | prior
    · rcases Prod.mk.inj same with ⟨rfl, rfl⟩
      exact ⟨clause, clauseAt, parent⟩
    · exact valid.1 other otherName prior
  · exact valid.2

theorem state_emit_input (problem : NamedProblem) (clauses : List Clause) (state : CollectorState)
    (source : Nat) (name : String) (raw : Clause)
    (valid : StateInvariant problem clauses state)
    (rawAt : problem.signature.problem[source]? = some raw) (nameAt : problem.names[source]? = some name) :
    StateInvariant problem clauses
      (state.1 ++ [{ name, clause := raw, origin := .input source name }], state.2.1, source :: state.2.2) := by
  have appended := state_append problem clauses state
    [{ name, clause := raw, origin := .input source name }] valid
  refine ⟨appended.1, ?_⟩
  intro other member
  rcases List.mem_cons.mp member with same | prior
  · subst other
    exact ⟨raw, name, rawAt, nameAt,
      ⟨{ name, clause := raw, origin := .input source name }, by simp, rfl, rfl⟩⟩
  · exact appended.2 other prior

theorem state_emit_row (problem : NamedProblem) (clauses : List Clause) (state : CollectorState)
    (node : Nat) (row : Row) (valid : StateInvariant problem clauses state)
    (clauseAt : clauses[node]? = some row.clause) :
    StateInvariant problem clauses (state.1 ++ [row], (node, row.name) :: state.2.1, state.2.2) := by
  apply state_label problem clauses (state.1 ++ [row], state.2.1, state.2.2) node row.name row.clause
    (state_append problem clauses state [row] valid) clauseAt
  exact ⟨row, by simp, rfl, rfl⟩

end Fang.TstpExport.BuilderProof
