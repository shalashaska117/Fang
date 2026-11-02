/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent equality AST checker. No original-byte or Rust refinement claim. -/
import Factoring
import CommonRules
import Renaming

namespace Fang.Equality

abbrev Problem := List Clause

def models {D : Type} (model : Interpretation D) (problem : Problem) : Prop :=
  ∀ clause ∈ problem, clauseValid model clause

def Satisfiable (problem : Problem) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Interpretation D), models model problem

inductive UnaryRule where
  | factor (first second : Nat) (substitution : Subst)
  | equalityResolution (before after : Clause) (left right : Term) (substitution : Subst)
  | equalityFactoring (before after : Clause) (left right otherLeft otherRight : Term) (substitution : Subst)
  deriving Repr

inductive BinaryRule where
  | resolution (leftPosition rightPosition : Nat) (substitution : Subst)
  | paramodulation (equalityBefore equalityAfter targetBefore targetAfter : Clause)
      (left right : Term) (target : Literal) (substitution : Subst) (context : LiteralContext)
  deriving Repr

def inferUnary (premise claimed : Clause) : UnaryRule → Option Clause
  | .factor first second substitution => checkFactor premise first second substitution claimed
  | .equalityResolution before after left right substitution =>
      checkEqualityResolution premise before after left right substitution
  | .equalityFactoring before after left right otherLeft otherRight substitution =>
      checkEqualityFactoring premise before after left right otherLeft otherRight substitution

/-- Binary witnesses refer to disjoint even/odd parent variable namespaces. -/
def inferBinary (leftParent rightParent claimed : Clause) : BinaryRule → Option Clause
  | .resolution leftPosition rightPosition substitution =>
      checkResolution leftParent rightParent leftPosition rightPosition substitution claimed
  | .paramodulation equalityBefore equalityAfter targetBefore targetAfter left right target substitution context =>
      checkParamodulation (leftParent.map (Literal.rename Fang.leftRename))
        (rightParent.map (Literal.rename Fang.rightRename)) equalityBefore equalityAfter targetBefore targetAfter
        left right target substitution context

theorem inferUnary_sound {D : Type} (model : Interpretation D) (premise claimed output : Clause)
    (rule : UnaryRule) (valid : clauseValid model premise)
    (accepted : inferUnary premise claimed rule = some output) : clauseValid model output := by
  cases rule with
  | factor first second substitution =>
    exact checkFactor_sound model premise claimed output first second substitution valid accepted
  | equalityResolution before after left right substitution =>
    exact checkEqualityResolution_sound model premise before after output left right substitution valid accepted
  | equalityFactoring before after left right otherLeft otherRight substitution =>
    exact checkEqualityFactoring_sound model premise before after output left right otherLeft otherRight
      substitution valid accepted

theorem inferBinary_sound {D : Type} (model : Interpretation D) (leftParent rightParent claimed output : Clause)
    (rule : BinaryRule) (leftValid : clauseValid model leftParent) (rightValid : clauseValid model rightParent)
    (accepted : inferBinary leftParent rightParent claimed rule = some output) : clauseValid model output := by
  cases rule with
  | resolution leftPosition rightPosition substitution =>
    exact checkResolution_sound model leftParent rightParent claimed output leftPosition rightPosition
      substitution leftValid rightValid accepted
  | paramodulation equalityBefore equalityAfter targetBefore targetAfter left right target substitution context =>
    exact checkParamodulation_sound model _ _ equalityBefore equalityAfter targetBefore targetAfter output
      left right target substitution context (clause_valid_rename model Fang.leftRename leftParent leftValid)
      (clause_valid_rename model Fang.rightRename rightParent rightValid) accepted

inductive TraceError where
  | inputIndex (index : Nat)
  | parentIndex (index : Nat)
  | inferenceWitness
  | claimedClause
  | finalIndex
  | finalNotEmpty
  deriving DecidableEq, Repr

inductive Step where
  | input (index : Nat)
  | unary (parent : Nat) (rule : UnaryRule) (claimed : Clause)
  | binary (left right : Nat) (rule : BinaryRule) (claimed : Clause)
  deriving Repr

def Step.parents : Step → List Nat
  | .input _ => []
  | .unary parent _ _ => [parent]
  | .binary left right _ _ => [left, right]

structure Certificate where
  steps : List Step
  final : Nat
  deriving Repr

def fetch (clauses : List Clause) (index : Nat) (error : TraceError) : Except TraceError Clause :=
  match clauses[index]? with
  | none => .error error
  | some clause => .ok clause

theorem fetch_exact (clauses : List Clause) (index : Nat) (error : TraceError) (output : Clause)
    (accepted : fetch clauses index error = .ok output) : clauses[index]? = some output := by
  unfold fetch at accepted
  split at accepted
  next absent => contradiction
  next clause present => cases accepted; exact present

theorem fetch_bound (clauses : List Clause) (index : Nat) (error : TraceError) (output : Clause)
    (accepted : fetch clauses index error = .ok output) : index < clauses.length := by
  by_cases inside : index < clauses.length
  · exact inside
  · have absent : clauses[index]? = none := List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt inside)
    rw [fetch_exact clauses index error output accepted] at absent
    contradiction

def requireClaim (result : Option Clause) (claimed : Clause) : Except TraceError Clause :=
  match result with
  | none => .error .inferenceWitness
  | some actual => if actual = claimed then .ok actual else .error .claimedClause

theorem requireClaim_exact (result : Option Clause) (claimed output : Clause)
    (accepted : requireClaim result claimed = .ok output) : result = some output ∧ output = claimed := by
  cases result with
  | none => contradiction
  | some actual =>
    simp only [requireClaim] at accepted
    split at accepted
    next same => cases accepted; exact ⟨rfl, same⟩
    next different => contradiction

def checkStep (problem : Problem) (checked : List Clause) : Step → Except TraceError Clause
  | .input index => fetch problem index (.inputIndex index)
  | .unary parent rule claimed => do
      let premise ← fetch checked parent (.parentIndex parent)
      requireClaim (inferUnary premise claimed rule) claimed
  | .binary left right rule claimed => do
      let leftParent ← fetch checked left (.parentIndex left)
      let rightParent ← fetch checked right (.parentIndex right)
      requireClaim (inferBinary leftParent rightParent claimed rule) claimed

theorem checkStep_sound {D : Type} (model : Interpretation D) (problem : Problem) (checked : List Clause)
    (step : Step) (output : Clause) (original : models model problem)
    (previous : ∀ clause ∈ checked, clauseValid model clause)
    (accepted : checkStep problem checked step = .ok output) : clauseValid model output := by
  cases step with
  | input index => exact original output (List.mem_iff_getElem?.mpr ⟨index, fetch_exact _ _ _ _ accepted⟩)
  | unary parent rule claimed =>
    simp only [checkStep] at accepted
    cases parentResult : fetch checked parent (.parentIndex parent) with
    | error error => simp [parentResult, bind, Except.bind] at accepted
    | ok premise =>
      simp only [parentResult, bind, Except.bind] at accepted
      exact inferUnary_sound model premise claimed output rule
        (previous premise (List.mem_iff_getElem?.mpr ⟨parent, fetch_exact _ _ _ _ parentResult⟩))
        (requireClaim_exact _ _ _ accepted).1
  | binary left right rule claimed =>
    simp only [checkStep] at accepted
    cases leftResult : fetch checked left (.parentIndex left) with
    | error error => simp [leftResult, bind, Except.bind] at accepted
    | ok leftParent =>
      simp only [leftResult, bind, Except.bind] at accepted
      cases rightResult : fetch checked right (.parentIndex right) with
      | error error => simp [rightResult, bind, Except.bind] at accepted
      | ok rightParent =>
        simp only [rightResult, bind, Except.bind] at accepted
        exact inferBinary_sound model leftParent rightParent claimed output rule
          (previous leftParent (List.mem_iff_getElem?.mpr ⟨left, fetch_exact _ _ _ _ leftResult⟩))
          (previous rightParent (List.mem_iff_getElem?.mpr ⟨right, fetch_exact _ _ _ _ rightResult⟩))
          (requireClaim_exact _ _ _ accepted).1

def checkSteps (problem : Problem) : List Clause → List Step → Except TraceError (List Clause)
  | checked, [] => .ok checked
  | checked, step :: rest => do
      let output ← checkStep problem checked step
      checkSteps problem (checked ++ [output]) rest

theorem checkStep_parents (problem : Problem) (checked : List Clause) (step : Step) (output : Clause)
    (accepted : checkStep problem checked step = .ok output) :
    ∀ parent ∈ step.parents, parent < checked.length := by
  cases step with
  | input index => simp [Step.parents]
  | unary parent rule claimed =>
    simp only [checkStep] at accepted
    cases parentResult : fetch checked parent (.parentIndex parent) with
    | error error => simp [parentResult, bind, Except.bind] at accepted
    | ok premise =>
      simpa [Step.parents] using fetch_bound checked parent (.parentIndex parent) premise parentResult
  | binary left right rule claimed =>
    simp only [checkStep] at accepted
    cases leftResult : fetch checked left (.parentIndex left) with
    | error error => simp [leftResult, bind, Except.bind] at accepted
    | ok leftParent =>
      simp only [leftResult, bind, Except.bind] at accepted
      cases rightResult : fetch checked right (.parentIndex right) with
      | error error => simp [rightResult, bind, Except.bind] at accepted
      | ok rightParent =>
        intro parent member
        simp only [Step.parents, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact fetch_bound checked _ _ leftParent leftResult
        · exact fetch_bound checked _ _ rightParent rightResult

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
  cases checkedResult : checkSteps problem [] certificate.steps with
  | error error => simp [checkedResult, bind, Except.bind] at accepted
  | ok checked =>
    simp only [checkedResult, bind, Except.bind] at accepted
    split at accepted
    next last =>
      split at accepted
      next empty =>
        exact ⟨checked, rfl, by simpa using checkSteps_length problem certificate.steps [] checked checkedResult,
          last, empty⟩
      next nonempty => contradiction
    next notLast => contradiction

theorem check_refutes (problem : Problem) (certificate : Certificate)
    (accepted : check problem certificate = .ok ()) : ¬ Satisfiable problem := by
  rintro ⟨D, ⟨element⟩, model, original⟩
  unfold check at accepted
  cases checkedResult : checkSteps problem [] certificate.steps with
  | error error => simp [checkedResult, bind, Except.bind] at accepted
  | ok checked =>
    simp only [checkedResult, bind, Except.bind] at accepted
    split at accepted
    next last =>
      split at accepted
      next empty =>
        have valid := checkSteps_sound model problem certificate.steps [] checked original (by simp) checkedResult
        have impossible := valid [] (List.mem_iff_getElem?.mpr ⟨certificate.final, empty⟩) (fun _ => element)
        obtain ⟨literal, member, _⟩ := impossible
        simp at member
      next nonempty => contradiction
    next notLast => contradiction

end Fang.Equality
