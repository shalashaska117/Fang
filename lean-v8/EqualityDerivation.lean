/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Bind each retained equality clause to its actual checked inference step. -/
import EqualityTrace

namespace Fang.QuantifiedEqualityTstp.Derivation
open Equality

abbrev Row := Ordered.Step × Equality.Clause

/-- Every row uses the exact preceding clauses, in their retained order. -/
inductive Checked (problem : Equality.Problem) : List Equality.Clause → List Row → Prop
  | nil (previous) : Checked problem previous []
  | cons {previous step clause rest}
      (accepted : Ordered.checkStep problem previous step = .ok clause)
      (later : Checked problem (previous ++ [clause]) rest) :
      Checked problem previous ((step, clause) :: rest)

def rows (output : Output) : List Row :=
  output.certificate.steps.zip output.clauses

theorem zip_projections (values : List Row) :
    (values.map Prod.fst).zip (values.map Prod.snd) = values := by
  induction values with
  | nil => rfl
  | cons value rest ih => cases value; simpa using ih

theorem checkSteps_rows {problem previous steps result}
    (accepted : Ordered.checkSteps problem previous steps = .ok result) :
    ∃ values : List Row, Checked problem previous values ∧
      values.map Prod.fst = steps ∧ previous ++ values.map Prod.snd = result := by
  induction steps generalizing previous with
  | nil =>
    have same : previous = result := Except.ok.inj accepted
    exact ⟨[], .nil previous, rfl, by simpa using same⟩
  | cons step rest ih =>
    cases current : Ordered.checkStep problem previous step with
    | error reason => simp [Ordered.checkSteps, current, Bind.bind, Except.bind] at accepted
    | ok clause =>
      have tail : Ordered.checkSteps problem (previous ++ [clause]) rest = .ok result := by
        simpa only [Ordered.checkSteps, current, Bind.bind, Except.bind] using accepted
      obtain ⟨values, checked, sameSteps, sameClauses⟩ := ih tail
      refine ⟨(step, clause) :: values, .cons current checked, ?_, ?_⟩
      · simp [sameSteps]
      · simpa [List.append_assoc] using sameClauses

theorem Checked.suffix {problem previous leading rest}
    (accepted : Checked problem previous (leading ++ rest)) :
    Checked problem (previous ++ leading.map Prod.snd) rest := by
  induction leading generalizing previous with
  | nil => simpa using accepted
  | cons value leading ih =>
    cases accepted with
    | cons first later =>
      simpa [List.append_assoc] using ih later

theorem Checked.row {problem previous leading value rest}
    (accepted : Checked problem previous (leading ++ value :: rest)) :
    Ordered.checkStep problem (previous ++ leading.map Prod.snd) value.1 = .ok value.2 := by
  have tail := accepted.suffix
  cases tail with
  | cons current _ => exact current

theorem Checked.parents {problem previous leading value rest}
    (accepted : Checked problem previous (leading ++ value :: rest)) :
    ∀ parent ∈ value.1.parents, parent < previous.length + leading.length := by
  have bounded := Ordered.checkStep_parents problem (previous ++ leading.map Prod.snd)
    value.1 value.2 accepted.row
  simpa using bounded

/-- The checked sequence has the same two projections as the retained output.
    Consequently zip cannot truncate a step or clause on successful build. -/
theorem build_rows {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output) :
    Checked output.prepared.problem [] (rows output) ∧
      (rows output).map Prod.fst = output.certificate.steps ∧
      (rows output).map Prod.snd = output.clauses := by
  obtain ⟨values, checked, sameSteps, sameClauses⟩ :=
    checkSteps_rows (build_endpoint success).1
  simp only [List.nil_append] at sameClauses
  have paired : rows output = values := by
    rw [rows, ← sameSteps, ← sameClauses, zip_projections]
  exact ⟨paired.symm ▸ checked, by simpa [paired] using sameSteps,
    by simpa [paired] using sameClauses⟩

theorem build_row_checked {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : rows output = leading ++ value :: rest) :
    Ordered.checkStep output.prepared.problem (leading.map Prod.snd) value.1 = .ok value.2 := by
  have checked := (build_rows success).1
  rw [position] at checked
  simpa using checked.row

theorem build_parent_before {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output)
    {leading value rest} (position : rows output = leading ++ value :: rest) :
    ∀ parent ∈ value.1.parents, parent < leading.length := by
  have checked := (build_rows success).1
  rw [position] at checked
  simpa using checked.parents

theorem build_row_valid {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output)
    {D : Type} (model : Interpretation D) (original : models model output.prepared.problem)
    {value : Row} (member : value ∈ rows output) : clauseValid model value.2 := by
  have clauses := (build_rows success).2.2
  apply build_clauses_valid success model original value.2
  rw [← clauses]
  exact List.mem_map.mpr ⟨value, member, rfl⟩

theorem build_input_clause {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output)
    {leading index clause rest}
    (position : rows output = leading ++ (.input index, clause) :: rest) :
    output.prepared.problem[index]? = some clause := by
  exact fetch_exact output.prepared.problem index (.inputIndex index) clause
    (build_row_checked success position)

theorem build_final_row {input proof limits maximumPredicates maximumLiterals output}
    (success : build input proof limits maximumPredicates maximumLiterals = .ok output) :
    (rows output).length = output.certificate.steps.length ∧
      output.certificate.final + 1 = (rows output).length ∧
      ((rows output)[output.certificate.final]?).map Prod.snd = some [] := by
  have projections := build_rows success
  have stepsLength := congrArg List.length projections.2.1
  have clausesLength := congrArg List.length projections.2.2
  simp only [List.length_map] at stepsLength clausesLength
  obtain ⟨_, _, last, empty⟩ := build_endpoint success
  rw [← clausesLength] at last
  rw [← projections.2.2] at empty
  exact ⟨stepsLength, last, by simpa using empty⟩

#print axioms Fang.QuantifiedEqualityTstp.Derivation.zip_projections
#print axioms Fang.QuantifiedEqualityTstp.Derivation.checkSteps_rows
#print axioms Fang.QuantifiedEqualityTstp.Derivation.Checked.suffix
#print axioms Fang.QuantifiedEqualityTstp.Derivation.Checked.row
#print axioms Fang.QuantifiedEqualityTstp.Derivation.Checked.parents
#print axioms Fang.QuantifiedEqualityTstp.Derivation.build_rows
#print axioms Fang.QuantifiedEqualityTstp.Derivation.build_row_checked
#print axioms Fang.QuantifiedEqualityTstp.Derivation.build_parent_before
#print axioms Fang.QuantifiedEqualityTstp.Derivation.build_row_valid
#print axioms Fang.QuantifiedEqualityTstp.Derivation.build_input_clause
#print axioms Fang.QuantifiedEqualityTstp.Derivation.build_final_row

end Fang.QuantifiedEqualityTstp.Derivation
