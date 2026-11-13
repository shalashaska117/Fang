/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent role policy and original-conjecture semantics. -/
import FofEncoding

namespace Fang.TptpCandidate.Roles

deriving instance DecidableEq for Except

inductive Role where
  | axiomRole | hypothesis | definition | assumption | lemma | theoremRole | corollary
  | conjecture | negatedConjecture | plain | typeRole | interpretation | logic | unknown
  deriving Repr, DecidableEq

inductive InputClass where
  | premise | goal | alreadyNegated
  deriving Repr, DecidableEq

inductive PolicyError where
  | unknownRole | unsupportedRole | unlinkedNegatedGoal
  deriving Repr, DecidableEq

def classify : Role → Except PolicyError InputClass
  | .axiomRole | .hypothesis | .definition | .lemma | .theoremRole | .corollary => .ok .premise
  | .conjecture => .ok .goal
  | .negatedConjecture => .ok .alreadyNegated
  | .unknown => .error .unknownRole
  | .assumption | .plain | .typeRole | .interpretation | .logic => .error .unsupportedRole

/-- Metadata is carried as one value, without rewriting names, spans or origins. -/
structure Declaration (Metadata Body : Type) where
  metadata : Metadata
  role : Role
  original : Body

structure Signed (Metadata Body : Type) where
  declaration : Declaration Metadata Body
  positive : Bool

def negative (declaration : Declaration Metadata Body) : Signed Metadata Body :=
  ⟨declaration, false⟩

def Signed.Holds (eval : Body → Prop) (signed : Signed Metadata Body) : Prop :=
  if signed.positive then eval signed.declaration.original else ¬ eval signed.declaration.original

theorem negative_original (declaration : Declaration Metadata Body) :
    (negative declaration).declaration = declaration := rfl

theorem negative_holds (eval : Body → Prop) (declaration : Declaration Metadata Body) :
    (negative declaration).Holds eval ↔ ¬ eval declaration.original := by rfl

def premises (source : List (Declaration Metadata Body)) : List (Declaration Metadata Body) :=
  source.filter (fun declaration => decide (classify declaration.role = .ok .premise))

def goals (source : List (Declaration Metadata Body)) : List (Declaration Metadata Body) :=
  source.filter (fun declaration => decide (declaration.role = .conjecture))

def positiveInputs (source : List (Declaration Metadata Body)) : List (Declaration Metadata Body) :=
  source.filter (fun declaration => decide (classify declaration.role = .ok .premise ∨
    classify declaration.role = .ok .alreadyNegated))

theorem goal_member {source : List (Declaration Metadata Body)} {declaration : Declaration Metadata Body} :
    declaration ∈ goals source ↔ declaration ∈ source ∧ declaration.role = .conjecture := by
  simp [goals]

theorem premise_member {source : List (Declaration Metadata Body)} {declaration : Declaration Metadata Body} :
    declaration ∈ premises source ↔ declaration ∈ source ∧ classify declaration.role = .ok .premise := by
  simp [premises]

theorem goal_not_premise {source : List (Declaration Metadata Body)} {declaration : Declaration Metadata Body}
    (goal : declaration ∈ goals source) : declaration ∉ premises source := by
  have role := (goal_member.mp goal).2
  intro member
  have classified := (premise_member.mp member).2
  simp [role, classify] at classified

def AllHold (eval : Model → Body → Prop) (source : List (Declaration Metadata Body)) (model : Model) : Prop :=
  ∀ declaration ∈ source, eval model declaration.original

def Countermodel (eval : Model → Body → Prop) (source : List (Declaration Metadata Body))
    (goal : Declaration Metadata Body) (model : Model) : Prop :=
  AllHold eval (premises source) model ∧ (negative goal).Holds (eval model)

def EntailsAll (eval : Model → Body → Prop) (source : List (Declaration Metadata Body)) : Prop :=
  ∀ goal ∈ goals source, ∀ model, AllHold eval (premises source) model → eval model goal.original

theorem obligation_models (eval : Model → Body → Prop) (source : List (Declaration Metadata Body))
    (goal : Declaration Metadata Body) (model : Model) :
    Countermodel eval source goal model ↔
      AllHold eval (premises source) model ∧ ¬ eval model goal.original := by rfl

/-- Every original conjecture has its own refutation obligation. -/
theorem all_refuted_iff_entails_all (eval : Model → Body → Prop)
    (source : List (Declaration Metadata Body)) :
    (∀ goal ∈ goals source, ¬ ∃ model, Countermodel eval source goal model) ↔
      EntailsAll eval source := by
  classical
  constructor
  · intro refuted goal member model axioms
    apply Classical.byContradiction
    intro falseGoal
    exact refuted goal member ⟨model, axioms, falseGoal⟩
  · intro entails goal member ⟨model, axioms, falseGoal⟩
    exact falseGoal (entails goal member model axioms)

theorem no_goals_vacuous (eval : Model → Body → Prop)
    {source : List (Declaration Metadata Body)} (empty : goals source = []) :
    EntailsAll eval source := by
  intro goal member
  simp [empty] at member

/-- Without an original goal, refuting the positive inputs proves only their
    unsatisfiability. An already-negated label supplies no original formula. -/
def SatisfiableInputs (eval : Model → Body → Prop) (source : List (Declaration Metadata Body)) : Prop :=
  ∃ model, AllHold eval (positiveInputs source) model

theorem refuted_inputs (eval : Model → Body → Prop) (source : List (Declaration Metadata Body))
    (refuted : ∀ model, ¬ AllHold eval (positiveInputs source) model) :
    ¬ SatisfiableInputs eval source := by
  rintro ⟨model, holds⟩
  exact refuted model holds

theorem already_negated_positive {source : List (Declaration Metadata Body)}
    {declaration : Declaration Metadata Body} (member : declaration ∈ source)
    (role : declaration.role = .negatedConjecture) : declaration ∈ positiveInputs source := by
  simp [positiveInputs, member, role, classify]

theorem negated_formula_holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) (body : FullFof.Formula) :
    (FullFof.Formula.neg body).Holds model valuation ↔ ¬ body.Holds model valuation := by rfl

theorem negated_formula_closed {body : FullFof.Formula} (closed : body.Within []) :
    (FullFof.Formula.neg body).Within [] := closed

/-- Encoding retains the same complete symbol and variable maps under negation. -/
theorem encode_negation (body : FullFof.Formula) (functions predicates : Arity.Table)
    (variables : Source.Variables) :
    (FullFof.Formula.neg body).encode functions predicates variables =
      .neg (body.encode functions predicates variables) := rfl

end Fang.TptpCandidate.Roles
