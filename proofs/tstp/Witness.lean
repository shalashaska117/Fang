/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import BuilderLoop

namespace Fang.TstpExport.BuilderProof

/-- The invariant needed for the collector's node-to-row label table. It is a
    hypothesis of branch lemmas until proved for the actual whole loop. -/
def LabelsMatch (clauses : List Clause) (rows : List Row) (labels : List (Nat × String)) : Prop :=
  ∀ node name, findLabel labels node = .ok name →
    ∃ clause, clauses[node]? = some clause ∧ Parent rows name clause

theorem parent_append (rows extra : List Row) (name : String) (clause : Clause)
    (parent : Parent rows name clause) : Parent (rows ++ extra) name clause := by
  obtain ⟨row, member, label, body⟩ := parent
  exact ⟨row, List.mem_append_left _ member, label, body⟩

theorem checked_input (problem : NamedProblem) (clauses : List Clause)
    (source : Nat) (raw result : Clause)
    (rawAt : problem.signature.problem[source]? = some raw)
    (checked : checkStep (preprocess problem.signature.problem) clauses (.input source) = some result) :
    result = dedup raw := by
  simp only [checkStep, preprocess, List.getElem?_map, rawAt, Option.map_some] at checked
  exact (Option.some.inj checked).symm

theorem input_row_justified (problem : NamedProblem) (rows : List Row)
    (source : Nat) (name : String) (raw : Clause)
    (rawAt : problem.signature.problem[source]? = some raw)
    (nameAt : problem.names[source]? = some name) :
    Justified problem rows { name, clause := raw, origin := .input source name } :=
  ⟨nameAt, rfl, rawAt⟩

theorem dedup_row_justified (problem : NamedProblem) (rows : List Row) (clauses : List Clause)
    (node source : Nat) (name : String) (raw result : Clause)
    (rawAt : problem.signature.problem[source]? = some raw)
    (parent : Parent rows name raw)
    (checked : checkStep (preprocess problem.signature.problem) clauses (.input source) = some result) :
    Justified problem rows { name := internalName node, clause := result, origin := .deduplicate node source name } :=
  ⟨raw, parent, rawAt, checked_input problem clauses source raw result rawAt checked⟩

theorem checked_factor (problem : Problem) (clauses : List Clause)
    (parent i j : Nat) (σ : Subst) (claimed result : Clause)
    (checked : checkStep problem clauses (.factor parent i j σ claimed) = some result) :
    ∃ premise, clauses[parent]? = some premise ∧ Fang.factor premise i j σ = some result ∧ result = claimed := by
  cases hp : clauses[parent]? with
  | none => simp [checkStep, hp] at checked
  | some premise =>
    cases hf : Fang.factor premise i j σ with
    | none => simp [checkStep, hp, hf] at checked
    | some found =>
      simp only [checkStep, hp, hf, bind, Option.bind] at checked
      split at checked
      next same =>
        have resultEq := Option.some.inj checked
        exact ⟨premise, rfl, by simpa [resultEq] using hf, resultEq.symm.trans same⟩
      next => simp_all

theorem checked_resolve (problem : Problem) (clauses : List Clause)
    (left i right j : Nat) (σ : Subst) (claimed result : Clause)
    (checked : checkStep problem clauses (.resolve left i right j σ claimed) = some result) :
    ∃ lc rc, clauses[left]? = some lc ∧ clauses[right]? = some rc ∧
      Fang.resolve lc i rc j σ = some result ∧ result = claimed := by
  cases hl : clauses[left]? with
  | none => simp [checkStep, hl] at checked
  | some lc =>
    cases hr : clauses[right]? with
    | none => simp [checkStep, hl, hr] at checked
    | some rc =>
      cases hs : Fang.resolve lc i rc j σ with
      | none => simp [checkStep, hl, hr, hs] at checked
      | some found =>
        simp only [checkStep, hl, hr, hs, bind, Option.bind] at checked
        split at checked
        next same =>
          have resultEq := Option.some.inj checked
          exact ⟨lc, rc, rfl, rfl, by simpa [resultEq] using hs, resultEq.symm.trans same⟩
        next => simp_all

theorem resolve_witness (left right result : Clause) (i j : Nat) (σ : Subst)
    (success : Fang.resolve left i right j σ = some result) :
    ResolutionWitness (left.map (Literal.rename leftRename)) i
      (right.map (Literal.rename rightRename)) j σ result := by
  unfold Fang.resolve at success
  cases hi : (left.map (Literal.rename leftRename))[i]? with
  | none => simp [hi] at success
  | some a =>
    cases hj : (right.map (Literal.rename rightRename))[j]? with
    | none => simp [hi, hj] at success
    | some b =>
      simp only [hi, hj, bind, Option.bind] at success
      split at success
      next witness =>
        exact ⟨a, b, hi, hj, witness.1, witness.2.1, witness.2.2, (Option.some.inj success).symm⟩
      next => simp_all

theorem factor_row_justified (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (rows : List Row) (labels : List (Nat × String))
    (node parent i j : Nat) (name : String) (σ : Subst) (claimed result : Clause)
    (trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses)
    (stepAt : certificate.steps[node]? = some (.factor parent i j σ claimed))
    (clauseAt : clauses[node]? = some result)
    (mapping : LabelsMatch clauses rows labels) (labelAt : findLabel labels parent = .ok name) :
    Justified problem rows { name := internalName node, clause := result, origin := .factor node i j name σ } := by
  obtain ⟨premise, premiseAt, inferred, _⟩ := checked_factor _ clauses parent i j σ claimed result
    (checked_trace_at _ certificate clauses trace node _ result stepAt clauseAt)
  obtain ⟨labelClause, labelClauseAt, labelParent⟩ := mapping parent name labelAt
  have same : labelClause = premise := Option.some.inj (labelClauseAt.symm.trans premiseAt)
  exact ⟨premise, by simpa [same] using labelParent, inferred⟩

def leftRow (node : Nat) (parent : String) (clause : Clause) : Row :=
  { name := s!"fang:left:{node}", clause := clause.map (Literal.rename leftRename),
    origin := .rename node false parent }

def rightRow (node : Nat) (parent : String) (clause : Clause) : Row :=
  { name := s!"fang:right:{node}", clause := clause.map (Literal.rename rightRename),
    origin := .rename node true parent }

def resolveRow (node i j : Nat) (σ : Subst) (result : Clause) : Row :=
  { name := internalName node, clause := result,
    origin := .resolve node i j s!"fang:left:{node}" s!"fang:right:{node}" σ }

/-- The exact three-row block used by the real resolution branch is justified
    once the incoming label-table invariant is available. -/
theorem resolution_rows_justified (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (rows : List Row) (labels : List (Nat × String))
    (node left i right j : Nat) (leftName rightName : String) (σ : Subst)
    (claimed result lc rc : Clause)
    (trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses)
    (stepAt : certificate.steps[node]? = some (.resolve left i right j σ claimed))
    (clauseAt : clauses[node]? = some result)
    (leftAt : clauses[left]? = some lc) (rightAt : clauses[right]? = some rc)
    (mapping : LabelsMatch clauses rows labels)
    (leftLabel : findLabel labels left = .ok leftName)
    (rightLabel : findLabel labels right = .ok rightName) :
    Justified problem rows (leftRow node leftName lc) ∧
    Justified problem (rows ++ [leftRow node leftName lc]) (rightRow node rightName rc) ∧
    Justified problem (rows ++ [leftRow node leftName lc, rightRow node rightName rc])
      (resolveRow node i j σ result) := by
  obtain ⟨lp, lpAt, lpParent⟩ := mapping left leftName leftLabel
  obtain ⟨rp, rpAt, rpParent⟩ := mapping right rightName rightLabel
  have le : lp = lc := Option.some.inj (lpAt.symm.trans leftAt)
  have re : rp = rc := Option.some.inj (rpAt.symm.trans rightAt)
  subst lp
  subst rp
  obtain ⟨leftChecked, rightChecked, leftCheckedAt, rightCheckedAt, inferred, _⟩ :=
    checked_resolve _ clauses left i right j σ claimed result
      (checked_trace_at _ certificate clauses trace node _ result stepAt clauseAt)
  have cle : leftChecked = lc := Option.some.inj (leftCheckedAt.symm.trans leftAt)
  have cre : rightChecked = rc := Option.some.inj (rightCheckedAt.symm.trans rightAt)
  subst leftChecked
  subst rightChecked
  refine ⟨⟨lc, lpParent, rfl⟩, ⟨rc, parent_append _ _ _ _ rpParent, rfl⟩, ?_⟩
  refine ⟨lc.map (Literal.rename leftRename), rc.map (Literal.rename rightRename), ?_, ?_,
    resolve_witness lc rc result i j σ inferred⟩
  · exact ⟨leftRow node leftName lc, by simp, rfl, rfl⟩
  · exact ⟨rightRow node rightName rc, by simp, rfl, rfl⟩

end Fang.TstpExport.BuilderProof
