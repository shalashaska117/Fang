/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Additive AST trace dialect. The old paramodulation node keeps its old meaning. -/
import Trace
import OrderedRule

namespace Fang.Equality.Ordered

inductive Step where
  | input (index : Nat)
  | factor (parent first second : Nat) (substitution : Subst) (claimed : Clause)
  | equalityResolution (parent : Nat) (before after : Clause) (left right : Term)
      (substitution : Subst) (claimed : Clause)
  | resolution (left leftPosition right rightPosition : Nat) (substitution : Subst) (claimed : Clause)
  | paramodulation (source target : Nat) (witness : Witness) (claimed : Clause)
  deriving Repr

def Step.parents : Step → List Nat
  | .input _ => []
  | .factor parent _ _ _ _ | .equalityResolution parent _ _ _ _ _ _ => [parent]
  | .resolution left _ right _ _ _ | .paramodulation left right _ _ => [left, right]

structure Certificate where
  steps : List Step
  final : Nat
  deriving Repr

def checkStep (problem : Problem) (checked : List Clause) : Step → Except TraceError Clause
  | .input index => Equality.checkStep problem checked (.input index)
  | .factor parent first second substitution claimed =>
      Equality.checkStep problem checked (.unary parent (.factor first second substitution) claimed)
  | .equalityResolution parent before after left right substitution claimed =>
      Equality.checkStep problem checked (.unary parent (.equalityResolution before after left right substitution) claimed)
  | .resolution left leftPosition right rightPosition substitution claimed =>
      Equality.checkStep problem checked (.binary left right (.resolution leftPosition rightPosition substitution) claimed)
  | .paramodulation source target witness claimed => do
      let sourceClause ← fetch checked source (.parentIndex source)
      let targetClause ← fetch checked target (.parentIndex target)
      requireClaim (infer sourceClause targetClause witness) claimed

theorem checkStep_sound {D : Type} (model : Interpretation D) (problem : Problem) (checked : List Clause)
    (step : Step) (output : Clause) (original : models model problem)
    (previous : ∀ clause ∈ checked, clauseValid model clause)
    (accepted : checkStep problem checked step = .ok output) : clauseValid model output := by
  cases step with
  | input index | factor parent first second substitution claimed
    | equalityResolution parent before after left right substitution claimed
    | resolution left leftPosition right rightPosition substitution claimed =>
    simp only [checkStep] at accepted
    exact Equality.checkStep_sound model problem checked _ output original previous accepted
  | paramodulation source target witness claimed =>
    simp only [checkStep] at accepted
    cases sourceRun : fetch checked source (.parentIndex source) with
    | error error => simp [sourceRun, bind, Except.bind] at accepted
    | ok sourceClause =>
      simp only [sourceRun, bind, Except.bind] at accepted
      cases targetRun : fetch checked target (.parentIndex target) with
      | error error => simp [targetRun] at accepted
      | ok targetClause =>
        simp only [targetRun] at accepted
        exact infer_sound model sourceClause targetClause output witness
          (previous sourceClause (List.mem_iff_getElem?.mpr ⟨source, fetch_exact _ _ _ _ sourceRun⟩))
          (previous targetClause (List.mem_iff_getElem?.mpr ⟨target, fetch_exact _ _ _ _ targetRun⟩))
          (requireClaim_exact _ _ _ accepted).1

theorem checkStep_parents (problem : Problem) (checked : List Clause) (step : Step) (output : Clause)
    (accepted : checkStep problem checked step = .ok output) :
    ∀ parent ∈ step.parents, parent < checked.length := by
  cases step with
  | input index => simp [Step.parents]
  | factor parent first second substitution claimed
    | equalityResolution parent before after left right substitution claimed
    | resolution left leftPosition right rightPosition substitution claimed =>
    simp only [checkStep] at accepted
    exact Equality.checkStep_parents problem checked _ output accepted
  | paramodulation source target witness claimed =>
    simp only [checkStep] at accepted
    cases sourceRun : fetch checked source (.parentIndex source) with
    | error error => simp [sourceRun, bind, Except.bind] at accepted
    | ok sourceClause =>
      simp only [sourceRun, bind, Except.bind] at accepted
      cases targetRun : fetch checked target (.parentIndex target) with
      | error error => simp [targetRun] at accepted
      | ok targetClause =>
        intro parent member
        simp only [Step.parents, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact fetch_bound checked _ _ sourceClause sourceRun
        · exact fetch_bound checked _ _ targetClause targetRun

def checkSteps (problem : Problem) : List Clause → List Step → Except TraceError (List Clause)
  | checked, [] => .ok checked
  | checked, step :: rest => do
      let output ← checkStep problem checked step
      checkSteps problem (checked ++ [output]) rest

theorem checkSteps_length (problem : Problem) (steps : List Step) (checked result : List Clause)
    (accepted : checkSteps problem checked steps = .ok result) :
    result.length = checked.length + steps.length := by
  induction steps generalizing checked result with
  | nil => cases accepted; simp
  | cons step rest ih =>
    simp only [checkSteps] at accepted
    cases current : checkStep problem checked step with
    | error error => simp [current, bind, Except.bind] at accepted
    | ok output =>
      simp only [current, bind, Except.bind] at accepted
      have length := ih (checked ++ [output]) result accepted
      simp only [List.length_append, List.length_cons, List.length_nil] at length ⊢
      omega

theorem checkSteps_sound {D : Type} (model : Interpretation D) (problem : Problem)
    (steps : List Step) (checked result : List Clause) (original : models model problem)
    (previous : ∀ clause ∈ checked, clauseValid model clause)
    (accepted : checkSteps problem checked steps = .ok result) :
    ∀ clause ∈ result, clauseValid model clause := by
  induction steps generalizing checked result with
  | nil => cases accepted; exact previous
  | cons step rest ih =>
    simp only [checkSteps] at accepted
    cases current : checkStep problem checked step with
    | error error => simp [current, bind, Except.bind] at accepted
    | ok output =>
      simp only [current, bind, Except.bind] at accepted
      apply ih (checked ++ [output]) result ?_ accepted
      intro clause member
      rcases List.mem_append.mp member with old | new
      · exact previous clause old
      · have same : clause = output := List.mem_singleton.mp new
        subst clause
        exact checkStep_sound model problem checked step output original previous current

def check (problem : Problem) (certificate : Certificate) : Except TraceError Unit := do
  let checked ← checkSteps problem [] certificate.steps
  if certificate.final + 1 = checked.length then
    if checked[certificate.final]? = some [] then .ok () else .error .finalNotEmpty
  else .error .finalIndex

theorem check_endpoint (problem : Problem) (certificate : Certificate)
    (accepted : check problem certificate = .ok ()) :
    ∃ checked, checkSteps problem [] certificate.steps = .ok checked ∧
      checked.length = certificate.steps.length ∧ certificate.final + 1 = checked.length ∧
      checked[certificate.final]? = some [] := by
  unfold check at accepted
  cases checkedRun : checkSteps problem [] certificate.steps with
  | error error => simp [checkedRun, bind, Except.bind] at accepted
  | ok checked =>
    simp only [checkedRun, bind, Except.bind] at accepted
    split at accepted
    next last =>
      split at accepted
      next empty => exact ⟨checked, rfl, by simpa using checkSteps_length problem certificate.steps [] checked checkedRun,
        last, empty⟩
      next nonempty => contradiction
    next notLast => contradiction

/-- A fresh dialect-level empty-clause result. No source-byte decoding or search
    completeness follows from this independent AST theorem. -/
theorem check_unsat (problem : Problem) (certificate : Certificate)
    (accepted : check problem certificate = .ok ()) : ¬ Satisfiable problem := by
  rintro ⟨D, nonempty, model, original⟩
  obtain ⟨checked, checkedRun, _, _, finalEmpty⟩ := check_endpoint problem certificate accepted
  have valid := checkSteps_sound model problem certificate.steps [] checked original (by simp) checkedRun
    [] (List.mem_iff_getElem?.mpr ⟨certificate.final, finalEmpty⟩)
  obtain ⟨value⟩ := nonempty
  have impossible := valid (fun _ => value)
  simp [clauseHolds] at impossible

end Fang.Equality.Ordered
