/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see the repository LICENSE.

Independent checker specification for Boolean preprocessing over first-order
atoms. This is not generated Rust and does not verify the Rust implementation.
-/
import Fang.Logic

namespace Fang.GroundFOF

inductive Formula where
  | atom : Atom → Formula
  | truth : Formula
  | falsity : Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  deriving Repr

inductive Nnf where
  | lit : Literal → Nnf
  | truth : Nnf
  | falsity : Nnf
  | conj : Nnf → Nnf → Nnf
  | disj : Nnf → Nnf → Nnf
  deriving Repr

def Formula.Holds {D : Type} (M : Interpretation D) (ρ : Nat → D) : Formula → Prop
  | .atom a => a.Holds M ρ
  | .truth => True
  | .falsity => False
  | .neg a => ¬ a.Holds M ρ
  | .conj a b => a.Holds M ρ ∧ b.Holds M ρ
  | .disj a b => a.Holds M ρ ∨ b.Holds M ρ
  | .implies a b => a.Holds M ρ → b.Holds M ρ

def Nnf.Holds {D : Type} (M : Interpretation D) (ρ : Nat → D) : Nnf → Prop
  | .lit l => l.Holds M ρ
  | .truth => True
  | .falsity => False
  | .conj a b => a.Holds M ρ ∧ b.Holds M ρ
  | .disj a b => a.Holds M ρ ∨ b.Holds M ρ

def signed (positive : Bool) (p : Prop) : Prop :=
  if positive then p else ¬ p

def Formula.nnf : Formula → Bool → Nnf
  | .atom a, p => .lit ⟨p, a⟩
  | .truth, p => if p then .truth else .falsity
  | .falsity, p => if p then .falsity else .truth
  | .neg a, p => a.nnf (!p)
  | .conj a b, p =>
      if p then .conj (a.nnf true) (b.nnf true)
      else .disj (a.nnf false) (b.nnf false)
  | .disj a b, p =>
      if p then .disj (a.nnf true) (b.nnf true)
      else .conj (a.nnf false) (b.nnf false)
  | .implies a b, p =>
      if p then .disj (a.nnf false) (b.nnf true)
      else .conj (a.nnf true) (b.nnf false)

theorem neg_conj (p q : Prop) : (¬ (p ∧ q)) ↔ (¬ p ∨ ¬ q) := by
  classical
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inr (fun hq => h ⟨hp, hq⟩)
    · exact Or.inl hp
  · intro h hpq
    cases h with
    | inl hn => exact hn hpq.1
    | inr hn => exact hn hpq.2

theorem implication_as_disj (p q : Prop) : (p → q) ↔ (¬ p ∨ q) := by
  classical
  constructor
  · intro h
    by_cases hp : p
    · exact Or.inr (h hp)
    · exact Or.inl hp
  · intro h hp
    cases h with
    | inl hn => exact False.elim (hn hp)
    | inr hq => exact hq

theorem neg_implication (p q : Prop) : (¬ (p → q)) ↔ (p ∧ ¬ q) := by
  classical
  rw [implication_as_disj]
  simp

theorem nnf_holds {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (f : Formula) (positive : Bool) :
    (f.nnf positive).Holds M ρ ↔ signed positive (f.Holds M ρ) := by
  classical
  induction f generalizing positive with
  | atom a => cases positive <;> rfl
  | truth => cases positive <;> simp [Formula.nnf, Nnf.Holds, Formula.Holds, signed]
  | falsity => cases positive <;> simp [Formula.nnf, Nnf.Holds, Formula.Holds, signed]
  | neg a ih =>
    cases positive <;> simp [Formula.nnf, Formula.Holds, ih, signed]
  | conj a b iha ihb =>
    cases positive <;>
      simp [Formula.nnf, Nnf.Holds, Formula.Holds, iha, ihb, signed, implication_as_disj]
  | disj a b iha ihb =>
    cases positive <;>
      simp [Formula.nnf, Nnf.Holds, Formula.Holds, iha, ihb, signed]
  | implies a b iha ihb =>
    cases positive <;>
      simp [Formula.nnf, Nnf.Holds, Formula.Holds, iha, ihb, signed,
        implication_as_disj]

/-- Left clauses are outermost; literal concatenation preserves both orders. -/
def clauseProduct (left right : Problem) : Problem :=
  left.flatMap (fun a => right.map (fun b => a ++ b))

def Nnf.clauses : Nnf → Problem
  | .lit l => [[l]]
  | .truth => []
  | .falsity => [[]]
  | .conj a b => a.clauses ++ b.clauses
  | .disj a b => clauseProduct a.clauses b.clauses

def HoldsAt {D : Type} (M : Interpretation D) (ρ : Nat → D) (p : Problem) : Prop :=
  ∀ c ∈ p, c.Holds M ρ

theorem clause_append_holds {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (a b : Clause) : (a ++ b).Holds M ρ ↔ a.Holds M ρ ∨ b.Holds M ρ := by
  simp only [Clause.Holds, List.mem_append]
  constructor
  · rintro ⟨l, hl, hh⟩
    cases hl with
    | inl ha => exact Or.inl ⟨l, ha, hh⟩
    | inr hb => exact Or.inr ⟨l, hb, hh⟩
  · intro h
    cases h with
    | inl ha => obtain ⟨l, hl, hh⟩ := ha; exact ⟨l, Or.inl hl, hh⟩
    | inr hb => obtain ⟨l, hl, hh⟩ := hb; exact ⟨l, Or.inr hl, hh⟩

theorem append_holdsAt {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (a b : Problem) : HoldsAt M ρ (a ++ b) ↔ HoldsAt M ρ a ∧ HoldsAt M ρ b := by
  simp [HoldsAt, List.mem_append, or_imp, forall_and]

theorem clauseProduct_holdsAt {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (a b : Problem) :
    HoldsAt M ρ (clauseProduct a b) ↔ HoldsAt M ρ a ∨ HoldsAt M ρ b := by
  classical
  have hproduct : HoldsAt M ρ (clauseProduct a b) ↔
      ∀ ca ∈ a, ∀ cb ∈ b, ca.Holds M ρ ∨ cb.Holds M ρ := by
    constructor
    · intro h ca hca cb hcb
      apply (clause_append_holds M ρ ca cb).mp
      apply h (ca ++ cb)
      exact List.mem_flatMap.mpr ⟨ca, hca, List.mem_map.mpr ⟨cb, hcb, rfl⟩⟩
    · intro h c hc
      obtain ⟨ca, hca, hmap⟩ := List.mem_flatMap.mp hc
      obtain ⟨cb, hcb, heq⟩ := List.mem_map.mp hmap
      subst c
      exact (clause_append_holds M ρ ca cb).mpr (h ca hca cb hcb)
  rw [hproduct]
  constructor
  · intro h
    by_cases ha : HoldsAt M ρ a
    · exact Or.inl ha
    · right
      intro cb hb
      apply Classical.byContradiction
      intro hn
      apply ha
      intro ca hca
      exact (h ca hca cb hb).resolve_right hn
  · intro h ca hca cb hcb
    cases h with
    | inl ha => exact Or.inl (ha ca hca)
    | inr hb => exact Or.inr (hb cb hcb)

theorem clauses_holdsAt {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (n : Nnf) : HoldsAt M ρ n.clauses ↔ n.Holds M ρ := by
  induction n with
  | lit l => simp [Nnf.clauses, HoldsAt, Clause.Holds, Nnf.Holds]
  | truth => simp [Nnf.clauses, HoldsAt, Nnf.Holds]
  | falsity => simp [Nnf.clauses, HoldsAt, Clause.Holds, Nnf.Holds]
  | conj a b iha ihb => simp [Nnf.clauses, Nnf.Holds, append_holdsAt, iha, ihb]
  | disj a b iha ihb => simp [Nnf.clauses, Nnf.Holds, clauseProduct_holdsAt, iha, ihb]

def Formula.clausify (f : Formula) : Problem := (f.nnf true).clauses

theorem clausify_holdsAt {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (f : Formula) : HoldsAt M ρ f.clausify ↔ f.Holds M ρ := by
  simpa [Formula.clausify, signed] using
    (clauses_holdsAt M ρ (f.nnf true)).trans (nnf_holds M ρ f true)

theorem models_iff_holdsAt {D : Type} (M : Interpretation D) (p : Problem) :
    p.Models M ↔ ∀ ρ, HoldsAt M ρ p := by
  constructor
  · intro h ρ c hc
    exact h c hc ρ
  · intro h c hc ρ
    exact h ρ c hc

/-- Universal closure is explicit here; this is not a FOF parser theorem. -/
theorem clausify_models {D : Type} (M : Interpretation D) (f : Formula) :
    f.clausify.Models M ↔ ∀ ρ, f.Holds M ρ := by
  simp only [models_iff_holdsAt, clausify_holdsAt]

end Fang.GroundFOF

#print axioms Fang.GroundFOF.nnf_holds
#print axioms Fang.GroundFOF.clause_append_holds
#print axioms Fang.GroundFOF.append_holdsAt
#print axioms Fang.GroundFOF.clauseProduct_holdsAt
#print axioms Fang.GroundFOF.clauses_holdsAt
#print axioms Fang.GroundFOF.clausify_holdsAt
#print axioms Fang.GroundFOF.models_iff_holdsAt
#print axioms Fang.GroundFOF.clausify_models
