/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE.
   Independent next-fragment specification. No executable Rust/byte-parser claim. -/
import GroundFormula

namespace Fang.QuantifiedFOF

inductive Formula where
  | atom : Atom → Formula
  | truth | falsity
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  | all : Nat → Formula → Formula
  | ex : Nat → Formula → Formula
  deriving Repr

inductive Nnf where
  | lit : Literal → Nnf
  | truth | falsity
  | conj : Nnf → Nnf → Nnf
  | disj : Nnf → Nnf → Nnf
  | all : Nat → Nnf → Nnf
  | ex : Nat → Nnf → Nnf
  deriving Repr

def update {D : Type} (valuation : Nat → D) (binder : Nat) (value : D) : Nat → D :=
  fun other => if other = binder then value else valuation other

def Formula.Holds {D : Type} (M : Interpretation D) (valuation : Nat → D) : Formula → Prop
  | .atom a => a.Holds M valuation
  | .truth => True
  | .falsity => False
  | .neg body => ¬ body.Holds M valuation
  | .conj left right => left.Holds M valuation ∧ right.Holds M valuation
  | .disj left right => left.Holds M valuation ∨ right.Holds M valuation
  | .implies left right => left.Holds M valuation → right.Holds M valuation
  | .all binder body => ∀ value : D, body.Holds M (update valuation binder value)
  | .ex binder body => ∃ value : D, body.Holds M (update valuation binder value)

def Nnf.Holds {D : Type} (M : Interpretation D) (valuation : Nat → D) : Nnf → Prop
  | .lit literal => literal.Holds M valuation
  | .truth => True
  | .falsity => False
  | .conj left right => left.Holds M valuation ∧ right.Holds M valuation
  | .disj left right => left.Holds M valuation ∨ right.Holds M valuation
  | .all binder body => ∀ value : D, body.Holds M (update valuation binder value)
  | .ex binder body => ∃ value : D, body.Holds M (update valuation binder value)

def Formula.nnf : Formula → Bool → Nnf
  | .atom a, positive => .lit ⟨positive, a⟩
  | .truth, positive => if positive then .truth else .falsity
  | .falsity, positive => if positive then .falsity else .truth
  | .neg body, positive => body.nnf (!positive)
  | .conj left right, positive =>
      if positive then .conj (left.nnf true) (right.nnf true)
      else .disj (left.nnf false) (right.nnf false)
  | .disj left right, positive =>
      if positive then .disj (left.nnf true) (right.nnf true)
      else .conj (left.nnf false) (right.nnf false)
  | .implies left right, positive =>
      if positive then .disj (left.nnf false) (right.nnf true)
      else .conj (left.nnf true) (right.nnf false)
  | .all binder body, positive =>
      if positive then .all binder (body.nnf true) else .ex binder (body.nnf false)
  | .ex binder body, positive =>
      if positive then .ex binder (body.nnf true) else .all binder (body.nnf false)

/-- Quantifier duality includes arbitrary nesting and lexical shadowing. -/
theorem nnf_holds {D : Type} (M : Interpretation D) (valuation : Nat → D)
    (formula : Formula) (positive : Bool) :
    (formula.nnf positive).Holds M valuation ↔ GroundFOF.signed positive (formula.Holds M valuation) := by
  classical
  induction formula generalizing positive valuation with
  | atom a => cases positive <;> rfl
  | truth => cases positive <;> simp [Formula.nnf, Nnf.Holds, Formula.Holds, GroundFOF.signed]
  | falsity => cases positive <;> simp [Formula.nnf, Nnf.Holds, Formula.Holds, GroundFOF.signed]
  | neg body ih => cases positive <;> simp [Formula.nnf, Formula.Holds, ih, GroundFOF.signed]
  | conj left right ihl ihr => cases positive <;>
      simp [Formula.nnf, Formula.Holds, Nnf.Holds, ihl, ihr, GroundFOF.signed, GroundFOF.implication_as_disj]
  | disj left right ihl ihr => cases positive <;>
      simp [Formula.nnf, Formula.Holds, Nnf.Holds, ihl, ihr, GroundFOF.signed]
  | implies left right ihl ihr => cases positive <;>
      simp [Formula.nnf, Formula.Holds, Nnf.Holds, ihl, ihr, GroundFOF.signed, GroundFOF.implication_as_disj]
  | all binder body ih => cases positive <;>
      simp [Formula.nnf, Formula.Holds, Nnf.Holds, ih, GroundFOF.signed]
  | ex binder body ih => cases positive <;>
      simp [Formula.nnf, Formula.Holds, Nnf.Holds, ih, GroundFOF.signed]

def TermWithin (bound : List Nat) : Term → Prop
  | .var binder => binder ∈ bound
  | .app _ args => ∀ term ∈ args, TermWithin bound term

def Formula.Within (bound : List Nat) : Formula → Prop
  | .atom a => ∀ term ∈ a.args, TermWithin bound term
  | .truth | .falsity => True
  | .neg body => body.Within bound
  | .conj left right | .disj left right | .implies left right => left.Within bound ∧ right.Within bound
  | .all binder body | .ex binder body => body.Within (binder :: bound)

def Nnf.Within (bound : List Nat) : Nnf → Prop
  | .lit literal => ∀ term ∈ literal.atom.args, TermWithin bound term
  | .truth | .falsity => True
  | .conj left right | .disj left right => left.Within bound ∧ right.Within bound
  | .all binder body | .ex binder body => body.Within (binder :: bound)

theorem nnf_within (formula : Formula) (positive : Bool) (bound : List Nat)
    (closed : formula.Within bound) : (formula.nnf positive).Within bound := by
  induction formula generalizing positive bound with
  | atom a => exact closed
  | truth => cases positive <;> trivial
  | falsity => cases positive <;> trivial
  | neg body ih => exact ih (!positive) bound closed
  | conj left right ihl ihr => cases positive <;> exact ⟨ihl _ _ closed.1, ihr _ _ closed.2⟩
  | disj left right ihl ihr => cases positive <;> exact ⟨ihl _ _ closed.1, ihr _ _ closed.2⟩
  | implies left right ihl ihr => cases positive <;> exact ⟨ihl _ _ closed.1, ihr _ _ closed.2⟩
  | all binder body ih => cases positive <;> exact ih _ _ closed
  | ex binder body ih => cases positive <;> exact ih _ _ closed

/-- The mathematical choice step; this does not assign a fresh function symbol. -/
theorem choice_function_iff {Environment D : Type} (relation : Environment → D → Prop) :
    (∀ environment, ∃ value, relation environment value) ↔
      ∃ witness : Environment → D, ∀ environment, relation environment (witness environment) := by
  classical
  constructor
  · intro existsValue
    exact ⟨fun environment => Classical.choose (existsValue environment),
      fun environment => Classical.choose_spec (existsValue environment)⟩
  · rintro ⟨witness, holds⟩ environment
    exact ⟨witness environment, holds environment⟩

/-- Refuting axioms together with a negated conjecture proves entailment. -/
theorem conjecture_refutation {D : Type} (M : Interpretation D) (valuation : Nat → D)
    (axioms : List Formula) (conjecture : Formula)
    (refutation : ¬ ((∀ premise ∈ axioms, premise.Holds M valuation) ∧
      (Formula.neg conjecture).Holds M valuation)) :
    (∀ premise ∈ axioms, premise.Holds M valuation) → conjecture.Holds M valuation := by
  classical
  intro models
  exact Classical.byContradiction (fun denied => refutation ⟨models, denied⟩)

end Fang.QuantifiedFOF
