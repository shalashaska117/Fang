/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Trace
import SourceLink

namespace Fang.TstpExport.BuilderProof

/-- Proof-side factoring of the actual collector. Its relationship to production
    code is the checked `build_eq_factored` theorem below, not a trusted copy. -/
def collectWith {α : Type} (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause)
    (next : List Row → List (Nat × String) → Except String α) : Except String α := do
  let needed := ancestors certificate
  let mut rows : List Row := []
  let mut labels : List (Nat × String) := []
  let mut emittedInputs : List Nat := []
  for (step, index) in certificate.steps.zipIdx do
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
  next rows labels

def collect (problem : NamedProblem) (certificate : Certificate) (clauses : List Clause) :
    Except String (List Row × List (Nat × String)) :=
  collectWith problem certificate clauses (fun rows labels => pure (rows, labels))

theorem collectWith_eq_bind {α : Type} (problem : NamedProblem) (certificate : Certificate)
    (clauses : List Clause) (next : List Row → List (Nat × String) → Except String α) :
    collectWith problem certificate clauses next =
      (do let (rows, labels) ← collect problem certificate clauses; next rows labels) := by
  simp only [collect, collectWith, bind_assoc, pure_bind]

def finish (problem : NamedProblem) (certificate : Certificate)
    (rows : List Row) (labels : List (Nat × String)) : Except String Export := do
  let finalName ← findLabel labels certificate.final
  if rows.getLast?.map Row.name != some finalName then
    throw "export-error: final row is not last"
  if rows.getLast?.map Row.clause != some [] then
    throw "export-error: final row is not false"
  pure { signature := problem, rows, finalName }

def factored (problem : NamedProblem) (certificate : Certificate) : Except String Export := do
  if certificate.steps.length > 1000 then
    throw "resource-exhaustion: export supports at most 1000 certificate nodes"
  if !certificateWellFormed problem.signature certificate then
    throw "invalid-certificate: unknown symbol or inconsistent arity"
  if !check (preprocess problem.signature.problem) certificate then
    throw "rejected-certificate"
  let some clauses := checkSteps (preprocess problem.signature.problem) [] certificate.steps
    | throw "export-error: checked clauses unavailable"
  collectWith problem certificate clauses (finish problem certificate)

theorem build_eq_factored (problem : NamedProblem) (certificate : Certificate) :
    build problem certificate = factored problem certificate := by
  rfl

/-- Successful actual builds expose a successful run of the checked collector.
    No row invariant is assumed in this theorem. -/
theorem build_collects {problem : NamedProblem} {certificate : Certificate} {output : Export}
    (success : build problem certificate = .ok output) :
    ∃ clauses rows labels,
      checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses ∧
      collect problem certificate clauses = .ok (rows, labels) ∧
      finish problem certificate rows labels = .ok output := by
  have checked := build_checked success
  by_cases length : certificate.steps.length > 1000
  · simp [build, length, bind, Except.bind, throw] at success
  by_cases wellFormed : certificateWellFormed problem.signature certificate = true
  · rw [build_eq_factored] at success
    simp only [factored, collectWith_eq_bind] at success
    cases trace : checkSteps (preprocess problem.signature.problem) [] certificate.steps with
    | none => simp [length, wellFormed, checked, trace, throw] at success
    | some clauses =>
      cases collected : collect problem certificate clauses with
      | error reason =>
        simp [length, wellFormed, checked, trace, collected, bind, Except.bind] at success
      | ok pair =>
        rcases pair with ⟨rows, labels⟩
        refine ⟨clauses, rows, labels, rfl, collected, ?_⟩
        simpa [length, wellFormed, checked, trace, collected, bind, Except.bind] using success
  · simp [build, length, wellFormed, bind, Except.bind, throw] at success

end Fang.TstpExport.BuilderProof
