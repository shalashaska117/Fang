/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

Independently written checker for explicit first-order inference witnesses.
-/
import Fang.Logic

namespace Fang

inductive Step where
  | input (clause : Nat)
  | factor (parent first second : Nat) (subst : Subst) (claimed : Clause)
  | resolve (left leftPos right rightPos : Nat) (subst : Subst) (claimed : Clause)
  deriving Repr

structure Certificate where
  steps : List Step
  final : Nat
  deriving Repr

def substUnique (σ : Subst) : Bool := decide (σ.map Prod.fst).Nodup

def factor (c : Clause) (i j : Nat) (σ : Subst) : Option Clause := do
  let a ← c[i]?
  let b ← c[j]?
  if i ≠ j ∧ a.positive = b.positive ∧ a.atom.subst σ = b.atom.subst σ ∧
      substUnique σ = true then
    some ((c.eraseIdx j).map (Literal.subst σ))
  else none

def resolve (left : Clause) (i : Nat) (right : Clause) (j : Nat)
    (σ : Subst) : Option Clause := do
  let lc := left.map (Literal.rename leftRename)
  let rc := right.map (Literal.rename rightRename)
  let a ← lc[i]?
  let b ← rc[j]?
  if a.positive ≠ b.positive ∧ a.atom.subst σ = b.atom.subst σ ∧
      substUnique σ = true then
    some (((lc.eraseIdx i).map (Literal.subst σ)) ++
          ((rc.eraseIdx j).map (Literal.subst σ)))
  else none

def checkStep (p : Problem) (checked : List Clause) : Step → Option Clause
  | .input i => p[i]?
  | .factor parent i j σ claimed => do
    let c ← checked[parent]?
    let result ← factor c i j σ
    if result = claimed then some result else none
  | .resolve left i right j σ claimed => do
    let lc ← checked[left]?
    let rc ← checked[right]?
    let result ← resolve lc i rc j σ
    if result = claimed then some result else none

def checkSteps (p : Problem) : List Clause → List Step → Option (List Clause)
  | checked, [] => some checked
  | checked, step :: rest => do
    let c ← checkStep p checked step
    checkSteps p (checked ++ [c]) rest

def check (p : Problem) (certificate : Certificate) : Bool :=
  match checkSteps p [] certificate.steps with
  | none => false
  | some checked => decide (certificate.final + 1 = checked.length ∧
      checked[certificate.final]? = some [])

theorem holds_split {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (c : Clause) (i : Nat) (a : Literal) (hi : c[i]? = some a)
    (h : c.Holds M ρ) : a.Holds M ρ ∨ Clause.Holds M ρ (c.eraseIdx i) := by
  obtain ⟨l, hl, hv⟩ := h
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hl
  by_cases he : k = i
  · subst k
    have : l = a := Option.some.inj (hk.symm.trans hi)
    subst l
    exact Or.inl hv
  · exact Or.inr ⟨l, List.mem_eraseIdx_iff_getElem?.mpr ⟨k, he, hk⟩, hv⟩

theorem holds_subst_map {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (σ : Subst) (c : Clause) :
    Clause.Holds M ρ (c.map (Literal.subst σ)) ↔
      c.Holds M (fun v => (lookup σ v).eval M ρ) := by
  simp only [Clause.Holds, List.mem_map]
  constructor
  · rintro ⟨l, ⟨l', hl', he⟩, hv⟩
    subst l
    exact ⟨l', hl', (Literal.holds_subst M ρ σ l').mp hv⟩
  · rintro ⟨l, hl, hv⟩
    exact ⟨l.subst σ, ⟨l, hl, rfl⟩, (Literal.holds_subst M ρ σ l).mpr hv⟩

theorem factor_valid {D : Type} (M : Interpretation D) (c out : Clause)
    (i j : Nat) (σ : Subst) (hc : c.Valid M) (hr : factor c i j σ = some out) :
    out.Valid M := by
  unfold factor at hr
  cases hi : c[i]? with
  | none => simp [hi] at hr
  | some a =>
    cases hj : c[j]? with
    | none => simp [hi, hj] at hr
    | some b =>
      simp only [hi, hj, bind, Option.bind] at hr
      split at hr
      next h =>
        have hout : out = (c.eraseIdx j).map (Literal.subst σ) := (Option.some.inj hr).symm
        subst out
        intro ρ
        apply (holds_subst_map M ρ σ (c.eraseIdx j)).mpr
        let ρ' := fun v => (lookup σ v).eval M ρ
        rcases holds_split M ρ' c j b hj (hc ρ') with hb | hrest
        · have hs : a.subst σ = b.subst σ := by
            cases a; cases b
            simp only [Literal.subst, Literal.mk.injEq] at *
            exact ⟨h.2.1, h.2.2.1⟩
          have ha : a.Holds M ρ' := by
            apply (Literal.holds_subst M ρ σ a).mp
            rw [hs]
            exact (Literal.holds_subst M ρ σ b).mpr hb
          exact ⟨a, List.mem_eraseIdx_iff_getElem?.mpr ⟨i, h.1, hi⟩, ha⟩
        · exact hrest
      next h => simp at hr

theorem opposite_inconsistent {D : Type} (M : Interpretation D) (ρ : Nat → D)
    (a b : Literal) (hp : a.positive ≠ b.positive) (ha : a.atom = b.atom)
    (hla : a.Holds M ρ) (hlb : b.Holds M ρ) : False := by
  cases a with | mk ap aa =>
    cases b with | mk bp ba =>
      cases ap <;> cases bp <;> simp_all [Literal.Holds]

theorem resolve_valid {D : Type} (M : Interpretation D) (left right out : Clause)
    (i j : Nat) (σ : Subst) (hl : left.Valid M) (hr : right.Valid M)
    (hresult : resolve left i right j σ = some out) : out.Valid M := by
  let lc := left.map (Literal.rename leftRename)
  let rc := right.map (Literal.rename rightRename)
  have hleft : Clause.Valid M lc := Clause.valid_rename M leftRename left hl
  have hright : Clause.Valid M rc := Clause.valid_rename M rightRename right hr
  change (do
    let a ← lc[i]?
    let b ← rc[j]?
    if a.positive ≠ b.positive ∧ a.atom.subst σ = b.atom.subst σ ∧ substUnique σ = true then
      some ((lc.eraseIdx i).map (Literal.subst σ) ++ (rc.eraseIdx j).map (Literal.subst σ))
    else none) = some out at hresult
  cases hi : lc[i]? with
  | none => simp [hi] at hresult
  | some a =>
    cases hj : rc[j]? with
    | none => simp [hi, hj] at hresult
    | some b =>
      simp only [hi, hj, bind, Option.bind] at hresult
      split at hresult
      next h =>
        have hout := (Option.some.inj hresult).symm
        subst out
        intro ρ
        let ρ' := fun v => (lookup σ v).eval M ρ
        rcases holds_split M ρ' lc i a hi (hleft ρ') with ha | hlrest
        · rcases holds_split M ρ' rc j b hj (hright ρ') with hb | hrrest
          · exact False.elim (opposite_inconsistent M ρ (a.subst σ) (b.subst σ)
              h.1 h.2.1 ((Literal.holds_subst M ρ σ a).mpr ha)
              ((Literal.holds_subst M ρ σ b).mpr hb))
          · obtain ⟨l, hm, hv⟩ := (holds_subst_map M ρ σ (rc.eraseIdx j)).mpr hrrest
            exact ⟨l, List.mem_append_right _ hm, hv⟩
        · obtain ⟨l, hm, hv⟩ := (holds_subst_map M ρ σ (lc.eraseIdx i)).mpr hlrest
          exact ⟨l, List.mem_append_left _ hm, hv⟩
      next h => simp at hresult

theorem checkStep_valid {D : Type} (M : Interpretation D) (p : Problem)
    (checked : List Clause) (step : Step) (out : Clause)
    (hp : p.Models M) (hc : ∀ c ∈ checked, c.Valid M)
    (hs : checkStep p checked step = some out) : out.Valid M := by
  cases step with
  | input i =>
    exact hp out (List.mem_iff_getElem?.mpr ⟨i, hs⟩)
  | factor parent i j σ claimed =>
    simp only [checkStep] at hs
    cases hparent : checked[parent]? with
    | none => simp [hparent] at hs
    | some c =>
      simp only [hparent, bind, Option.bind] at hs
      cases hf : factor c i j σ with
      | none => simp [hf] at hs
      | some result =>
        simp only [hf] at hs
        split at hs
        next _ =>
          have he := Option.some.inj hs
          subst out
          exact factor_valid M c result i j σ
            (hc c (List.mem_iff_getElem?.mpr ⟨parent, hparent⟩)) hf
        next _ => simp at hs
  | resolve left i right j σ claimed =>
    simp only [checkStep] at hs
    cases hleft : checked[left]? with
    | none => simp [hleft] at hs
    | some lc =>
      simp only [hleft, bind, Option.bind] at hs
      cases hright : checked[right]? with
      | none => simp [hright] at hs
      | some rc =>
        simp only [hright] at hs
        cases hr : resolve lc i rc j σ with
        | none => simp [hr] at hs
        | some result =>
          simp only [hr] at hs
          split at hs
          next _ =>
            have he := Option.some.inj hs
            subst out
            exact resolve_valid M lc rc result i j σ
              (hc lc (List.mem_iff_getElem?.mpr ⟨left, hleft⟩))
              (hc rc (List.mem_iff_getElem?.mpr ⟨right, hright⟩)) hr
          next _ => simp at hs

theorem checkSteps_valid {D : Type} (M : Interpretation D) (p : Problem)
    (steps : List Step) (checked result : List Clause)
    (hp : p.Models M) (hc : ∀ c ∈ checked, c.Valid M)
    (hs : checkSteps p checked steps = some result) : ∀ c ∈ result, c.Valid M := by
  induction steps generalizing checked result with
  | nil =>
    have he : checked = result := Option.some.inj hs
    subst result
    exact hc
  | cons step rest ih =>
    simp only [checkSteps] at hs
    cases hstep : checkStep p checked step with
    | none => simp [hstep] at hs
    | some c =>
      simp only [hstep, bind, Option.bind] at hs
      apply ih (checked ++ [c]) result ?_ hs
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hc d hd
      · have he : d = c := List.mem_singleton.mp hd
        subst d
        exact checkStep_valid M p checked step c hp hc hstep

/-- Every accepted certificate refutes its supplied problem AST. -/
theorem check_sound (p : Problem) (certificate : Certificate)
    (h : check p certificate = true) : ¬ Satisfiable p := by
  rintro ⟨D, ⟨d⟩, M, hp⟩
  unfold check at h
  cases hs : checkSteps p [] certificate.steps with
  | none => simp [hs] at h
  | some checked =>
    simp only [hs, decide_eq_true_eq] at h
    have hc := checkSteps_valid M p certificate.steps [] checked hp (by simp) hs
    have he : Clause.Valid M [] := hc [] (List.mem_iff_getElem?.mpr ⟨certificate.final, h.2⟩)
    obtain ⟨l, hl, _⟩ := he (fun _ => d)
    simp at hl

/-- Preprocessing is proved here; the caller still owes input decoding semantics. -/
theorem check_preprocessed_sound (p : Problem) (certificate : Certificate)
    (h : check (preprocess p) certificate = true) : ¬ Satisfiable p := by
  intro hs
  exact check_sound (preprocess p) certificate h ((preprocess_preserves_satisfiable p).mpr hs)

end Fang
