/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import MixedPreprocess

namespace Fang.GroundFOF

def GroundTerm : Term → Prop
  | .var _ => False
  | .app _ arguments => ∀ t ∈ arguments, GroundTerm t

def GroundAtom (a : Atom) : Prop := ∀ t ∈ a.args, GroundTerm t

def Formula.Ground : Formula → Prop
  | .atom a => GroundAtom a
  | .truth | .falsity => True
  | .neg a => a.Ground
  | .conj a b | .disj a b | .implies a b => a.Ground ∧ b.Ground

theorem ground_term_eval {D : Type} (M : Interpretation D) (ρ σ : Nat → D)
    (t : Term) (h : GroundTerm t) : t.eval M ρ = t.eval M σ := by
  cases t with
  | var _ => exact False.elim (by simpa only [GroundTerm] using h)
  | app f arguments =>
    simp only [GroundTerm] at h
    simp only [Term.eval]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact ground_term_eval M ρ σ a (h a ha)
termination_by sizeOf t

theorem ground_atom_holds {D : Type} (M : Interpretation D) (ρ σ : Nat → D)
    (a : Atom) (h : GroundAtom a) : a.Holds M ρ ↔ a.Holds M σ := by
  have he : a.args.map (Term.eval M ρ) = a.args.map (Term.eval M σ) := by
    apply List.map_congr_left
    intro t ht
    exact ground_term_eval M ρ σ t (h t ht)
  simp only [Atom.Holds, he]

theorem ground_formula_holds {D : Type} (M : Interpretation D) (ρ σ : Nat → D)
    (f : Formula) (h : f.Ground) : f.Holds M ρ ↔ f.Holds M σ := by
  induction f with
  | atom a => exact ground_atom_holds M ρ σ a h
  | truth => rfl
  | falsity => rfl
  | neg a ih => exact not_congr (ih h)
  | conj a b iha ihb =>
    simp only [Formula.Holds, iha h.1, ihb h.2]
  | disj a b iha ihb =>
    simp only [Formula.Holds, iha h.1, ihb h.2]
  | implies a b iha ihb =>
    simp only [Formula.Holds, iha h.1, ihb h.2]

theorem ground_clausify_models {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (f : Formula) (h : f.Ground) : f.clausify.Models M ↔ f.Holds M ρ := by
  rw [clausify_models]
  constructor
  · intro hf
    exact hf ρ
  · intro hf σ
    exact (ground_formula_holds M ρ σ f h).mp hf

end Fang.GroundFOF
