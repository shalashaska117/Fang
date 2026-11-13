/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

Independently written semantics and proofs for Fang's certificate calculus.
-/
import Std

namespace Fang

inductive Term where
  | var : Nat → Term
  | app : Nat → List Term → Term
  deriving BEq, Repr

mutual
def termDecEq (a b : Term) : Decidable (a = b) := by
  cases a with
  | var x =>
    cases b with
    | var y =>
      exact if h : x = y then isTrue (h ▸ rfl) else isFalse (fun he => h (Term.var.inj he))
    | app _ _ => exact isFalse (by intro h; cases h)
  | app f ts =>
    cases b with
    | var _ => exact isFalse (by intro h; cases h)
    | app g us =>
      match decEq f g, termsDecEq ts us with
      | isTrue hf, isTrue ht => exact isTrue (hf ▸ ht ▸ rfl)
      | isFalse hf, _ => exact isFalse (fun h => hf (Term.app.inj h).1)
      | _, isFalse ht => exact isFalse (fun h => ht (Term.app.inj h).2)
termination_by sizeOf a
def termsDecEq (a b : List Term) : Decidable (a = b) := by
  cases a with
  | nil =>
    cases b with
    | nil => exact isTrue rfl
    | cons _ _ => exact isFalse (by intro h; cases h)
  | cons x xs =>
    cases b with
    | nil => exact isFalse (by intro h; cases h)
    | cons y ys =>
      match termDecEq x y, termsDecEq xs ys with
      | isTrue hh, isTrue ht => exact isTrue (hh ▸ ht ▸ rfl)
      | isFalse hh, _ => exact isFalse (fun h => hh (List.cons.inj h).1)
      | _, isFalse ht => exact isFalse (fun h => ht (List.cons.inj h).2)
termination_by sizeOf a
end

instance : DecidableEq Term := termDecEq

structure Atom where
  pred : Nat
  args : List Term
  deriving DecidableEq, BEq, Repr

structure Literal where
  positive : Bool
  atom : Atom
  deriving DecidableEq, BEq, Repr

abbrev Clause := List Literal
abbrev Problem := List Clause
abbrev Subst := List (Nat × Term)

def lookup (σ : Subst) (v : Nat) : Term :=
  match σ.find? (fun p => p.1 == v) with
  | some p => p.2
  | none => .var v

mutual
def Term.subst (σ : Subst) : Term → Term
  | .var v => lookup σ v
  | .app f ts => .app f (termsSubst σ ts)
def termsSubst (σ : Subst) : List Term → List Term
  | [] => []
  | t :: ts => t.subst σ :: termsSubst σ ts
end

theorem termsSubst_eq_map (σ : Subst) (ts : List Term) :
    termsSubst σ ts = ts.map (Term.subst σ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [termsSubst, List.map_cons, ih]

def Atom.subst (σ : Subst) (a : Atom) : Atom :=
  ⟨a.pred, a.args.map (Term.subst σ)⟩

def Literal.subst (σ : Subst) (l : Literal) : Literal :=
  ⟨l.positive, l.atom.subst σ⟩

mutual
def Term.rename (r : Nat → Nat) : Term → Term
  | .var v => .var (r v)
  | .app f ts => .app f (termsRename r ts)
def termsRename (r : Nat → Nat) : List Term → List Term
  | [] => []
  | t :: ts => t.rename r :: termsRename r ts
end

theorem termsRename_eq_map (r : Nat → Nat) (ts : List Term) :
    termsRename r ts = ts.map (Term.rename r) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [termsRename, List.map_cons, ih]

def Atom.rename (r : Nat → Nat) (a : Atom) : Atom :=
  ⟨a.pred, a.args.map (Term.rename r)⟩

def Literal.rename (r : Nat → Nat) (l : Literal) : Literal :=
  ⟨l.positive, l.atom.rename r⟩

structure Interpretation (D : Type) where
  function : Nat → List D → D
  predicate : Nat → List D → Prop

def Term.eval {D : Type} (M : Interpretation D) (ρ : Nat → D) : Term → D
  | .var v => ρ v
  | .app f ts => M.function f (ts.map (Term.eval M ρ))

def Atom.Holds {D : Type} (M : Interpretation D) (ρ : Nat → D) (a : Atom) : Prop :=
  M.predicate a.pred (a.args.map (Term.eval M ρ))

def Literal.Holds {D : Type} (M : Interpretation D) (ρ : Nat → D) (l : Literal) : Prop :=
  if l.positive then l.atom.Holds M ρ else ¬ l.atom.Holds M ρ

def Clause.Holds {D : Type} (M : Interpretation D) (ρ : Nat → D) (c : Clause) : Prop :=
  ∃ l ∈ c, l.Holds M ρ

def Clause.Valid {D : Type} (M : Interpretation D) (c : Clause) : Prop :=
  ∀ ρ, c.Holds M ρ

def Problem.Models {D : Type} (M : Interpretation D) (p : Problem) : Prop :=
  ∀ c ∈ p, c.Valid M

def Satisfiable (p : Problem) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (M : Interpretation D), p.Models M

theorem Term.eval_subst {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (σ : Subst) (t : Term) :
    (t.subst σ).eval M ρ = t.eval M (fun v => (lookup σ v).eval M ρ) := by
  cases t with
  | var v => simp only [Term.subst, Term.eval]
  | app f ts =>
    simp only [Term.subst, termsSubst_eq_map, Term.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact Term.eval_subst M ρ σ t
termination_by sizeOf t

theorem Term.eval_rename {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (r : Nat → Nat) (t : Term) :
    (t.rename r).eval M ρ = t.eval M (fun v => ρ (r v)) := by
  cases t with
  | var v => simp only [Term.rename, Term.eval]
  | app f ts =>
    simp only [Term.rename, termsRename_eq_map, Term.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact Term.eval_rename M ρ r t
termination_by sizeOf t

theorem Literal.holds_subst {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (σ : Subst) (l : Literal) :
    (l.subst σ).Holds M ρ ↔ l.Holds M (fun v => (lookup σ v).eval M ρ) := by
  simp only [Literal.subst, Literal.Holds, Atom.subst, Atom.Holds, List.map_map]
  have he : List.map (fun t => (t.subst σ).eval M ρ) l.atom.args =
      List.map (fun t => t.eval M (fun v => (lookup σ v).eval M ρ)) l.atom.args := by
    apply List.map_congr_left
    intro t _
    exact Term.eval_subst M ρ σ t
  simp only [Function.comp_def, he]

theorem Literal.holds_rename {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (r : Nat → Nat) (l : Literal) :
    (l.rename r).Holds M ρ ↔ l.Holds M (fun v => ρ (r v)) := by
  simp only [Literal.rename, Literal.Holds, Atom.rename, Atom.Holds, List.map_map]
  have he : List.map (fun t => (t.rename r).eval M ρ) l.atom.args =
      List.map (fun t => t.eval M (fun v => ρ (r v))) l.atom.args := by
    apply List.map_congr_left
    intro t _
    exact Term.eval_rename M ρ r t
  simp only [Function.comp_def, he]

theorem Clause.valid_subst {D : Type} (M : Interpretation D) (σ : Subst)
    (c : Clause) (h : c.Valid M) : Clause.Valid M (c.map (Literal.subst σ)) := by
  intro ρ
  obtain ⟨l, hl, hv⟩ := h (fun v => (lookup σ v).eval M ρ)
  exact ⟨l.subst σ, List.mem_map.mpr ⟨l, hl, rfl⟩,
    (Literal.holds_subst M ρ σ l).mpr hv⟩

theorem Clause.valid_rename {D : Type} (M : Interpretation D) (r : Nat → Nat)
    (c : Clause) (h : c.Valid M) : Clause.Valid M (c.map (Literal.rename r)) := by
  intro ρ
  obtain ⟨l, hl, hv⟩ := h (fun v => ρ (r v))
  exact ⟨l.rename r, List.mem_map.mpr ⟨l, hl, rfl⟩,
    (Literal.holds_rename M ρ r l).mpr hv⟩

def leftRename (v : Nat) : Nat := 2 * v
def rightRename (v : Nat) : Nat := 2 * v + 1

theorem leftRename_injective : Function.Injective leftRename := by
  intro a b h
  simp only [leftRename] at h
  omega

theorem rightRename_injective : Function.Injective rightRename := by
  intro a b h
  simp only [rightRename] at h
  omega

theorem renames_disjoint (a b : Nat) : leftRename a ≠ rightRename b := by
  simp only [leftRename, rightRename]
  omega

/-- Keep the first occurrence of each structurally equal literal. -/
def dedup (c : Clause) : Clause :=
  letI : BEq Literal := ⟨fun a b => decide (a = b)⟩
  c.eraseDups

theorem mem_dedup (l : Literal) (c : Clause) : l ∈ dedup c ↔ l ∈ c := by
  letI : BEq Literal := ⟨fun a b => decide (a = b)⟩
  letI : LawfulBEq Literal := {
    eq_of_beq := by intro a b h; exact of_decide_eq_true h
    rfl := by intro a; exact decide_eq_true rfl }
  exact List.mem_eraseDups

def preprocess (p : Problem) : Problem := p.map dedup

theorem dedup_preserves_models {D : Type} (M : Interpretation D) (c : Clause) :
    Clause.Valid M (dedup c) ↔ c.Valid M := by
  simp only [Clause.Valid, Clause.Holds, mem_dedup]

theorem preprocess_preserves_models {D : Type} (M : Interpretation D) (p : Problem) :
    Problem.Models M (preprocess p) ↔ p.Models M := by
  simp only [Problem.Models, preprocess, List.mem_map]
  constructor
  · intro h c hc
    exact (dedup_preserves_models M c).mp (h (dedup c) ⟨c, hc, rfl⟩)
  · intro h c ⟨c', hc', he⟩
    subst c
    exact (dedup_preserves_models M c').mpr (h c' hc')

theorem preprocess_preserves_satisfiable (p : Problem) :
    Satisfiable (preprocess p) ↔ Satisfiable p := by
  constructor <;> rintro ⟨D, ne, M, h⟩
  · exact ⟨D, ne, M, (preprocess_preserves_models M p).mp h⟩
  · exact ⟨D, ne, M, (preprocess_preserves_models M p).mpr h⟩

end Fang
