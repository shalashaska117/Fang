/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Universal closure is explicit; no executable-remover claim. -/
import BinderSyntax

namespace Fang.QuantifiedFOF.BinderRemoval

def Agree {D : Type} (free : List Nat) (left right : Nat → D) : Prop :=
  ∀ id ∈ free, left id = right id

theorem agree_refl {D : Type} (free : List Nat) (valuation : Nat → D) :
    Agree free valuation valuation := fun _ _ => rfl

theorem term_eval_congr {D : Type} (model : Interpretation D) (free : List Nat)
    (term : Term) (within : TermWithin free term) (left right : Nat → D)
    (agree : Agree free left right) : term.eval model left = term.eval model right := by
  cases term with
  | var id =>
    simp only [TermWithin] at within
    simpa only [Term.eval] using agree id within
  | app symbol arguments =>
    simp only [TermWithin] at within
    simp only [Term.eval]
    congr 1
    exact List.map_congr_left (fun term member => term_eval_congr model free term
      (within term member) left right agree)
termination_by sizeOf term

theorem literal_holds_congr {D : Type} (model : Interpretation D) (free : List Nat)
    (literal : Literal) (within : ∀ term ∈ literal.atom.args, TermWithin free term)
    (left right : Nat → D) (agree : Agree free left right) :
    literal.Holds model left ↔ literal.Holds model right := by
  have arguments : literal.atom.args.map (Term.eval model left) =
      literal.atom.args.map (Term.eval model right) :=
    List.map_congr_left (fun term member => term_eval_congr model free term
      (within term member) left right agree)
  simp only [Literal.Holds, Atom.Holds, arguments]

theorem ground_holds_congr {D : Type} (model : Interpretation D) (free : List Nat)
    (formula : GroundFOF.Nnf) (within : GroundWithin free formula)
    (left right : Nat → D) (agree : Agree free left right) :
    formula.Holds model left ↔ formula.Holds model right := by
  induction formula with
  | lit literal => exact literal_holds_congr model free literal within left right agree
  | truth | falsity => rfl
  | conj l r il ir => exact and_congr (il within.1) (ir within.2)
  | disj l r il ir => exact or_congr (il within.1) (ir within.2)

/-- Independent binder sets let two countervaluations coexist. The external
    variables retain their common values. This is the disjunction scope step. -/
theorem disjunction_scope {D : Type} (model : Interpretation D) (free leftIds rightIds : List Nat)
    (left right : GroundFOF.Nnf) (leftWithin : GroundWithin (free ++ leftIds) left)
    (rightWithin : GroundWithin (free ++ rightIds) right)
    (fresh : ∀ id ∈ leftIds, id ∉ free)
    (disjoint : ∀ id ∈ leftIds, ∀ other ∈ rightIds, id ≠ other)
    (valuation : Nat → D) :
    ((∀ other, Agree free other valuation → left.Holds model other) ∨
      (∀ other, Agree free other valuation → right.Holds model other)) ↔
      ∀ other, Agree free other valuation →
        left.Holds model other ∨ right.Holds model other := by
  classical
  constructor
  · intro either other agrees
    exact either.elim (fun holds => Or.inl (holds other agrees)) (fun holds => Or.inr (holds other agrees))
  · intro holds
    by_cases allLeft : ∀ other, Agree free other valuation → left.Holds model other
    · exact Or.inl allLeft
    · right
      intro rightVal rightAgree
      apply Classical.byContradiction
      intro rightFalse
      have counter : ∃ leftVal, Agree free leftVal valuation ∧ ¬ left.Holds model leftVal := by
        apply Classical.byContradiction
        intro none
        apply allLeft
        intro candidate agrees
        apply Classical.byContradiction
        intro denied
        exact none ⟨candidate, agrees, denied⟩
      obtain ⟨leftVal, leftAgree, leftFalse⟩ := counter
      let mixed : Nat → D := fun id => if id ∈ leftIds then leftVal id else rightVal id
      have common : Agree free mixed valuation := by
        intro id member
        have absent : id ∉ leftIds := fun contained => fresh id contained member
        simpa [mixed, absent] using rightAgree id member
      have matchesLeft : Agree (free ++ leftIds) mixed leftVal := by
        intro id member
        rcases List.mem_append.mp member with external | bound
        · have absent : id ∉ leftIds := fun contained => fresh id contained external
          simpa [mixed, absent] using (rightAgree id external).trans (leftAgree id external).symm
        · simp [mixed, bound]
      have matchesRight : Agree (free ++ rightIds) mixed rightVal := by
        intro id member
        have absent : id ∉ leftIds := by
          intro contained
          rcases List.mem_append.mp member with external | bound
          · exact fresh id contained external
          · exact disjoint id contained id bound rfl
        simp [mixed, absent]
      rcases holds mixed common with leftHolds | rightHolds
      · exact leftFalse ((ground_holds_congr model _ left leftWithin mixed leftVal matchesLeft).mp leftHolds)
      · exact rightFalse ((ground_holds_congr model _ right rightWithin mixed rightVal matchesRight).mp rightHolds)

/-- Pointwise semantics of the retained external variables. All removed binder
    values are universally quantified, including unused binders. -/
theorem Erases.holds_iff {D : Type} (model : Interpretation D) {source target}
    (erased : Erases source target) (free : List Nat) (safe : RectifiedWithin free source)
    (valuation : Nat → D) :
    source.Holds model valuation ↔
      ∀ other, Agree free other valuation → target.Holds model other := by
  induction erased generalizing free valuation with
  | lit literal =>
    constructor
    · intro holds other agrees
      exact (literal_holds_congr model free literal safe.1 other valuation agrees).mpr holds
    · intro holds
      exact holds valuation (agree_refl free valuation)
  | truth => exact ⟨fun _ _ _ => trivial, fun _ => trivial⟩
  | falsity => exact ⟨fun impossible => False.elim impossible, fun holds => holds valuation (agree_refl free valuation)⟩
  | @conj left right l r el er il ir =>
    obtain ⟨leftSafe, rightSafe, _⟩ := rectified_binary safe.1 safe.2.1 safe.2.2
    change (left.Holds model valuation ∧ right.Holds model valuation) ↔ _
    rw [il free leftSafe valuation, ir free rightSafe valuation]
    constructor
    · rintro ⟨hl, hr⟩ other agrees
      exact ⟨hl other agrees, hr other agrees⟩
    · intro both
      exact ⟨fun other agrees => (both other agrees).1, fun other agrees => (both other agrees).2⟩
  | @disj left right l r el er il ir =>
    obtain ⟨leftSafe, rightSafe, disjoint⟩ := rectified_binary safe.1 safe.2.1 safe.2.2
    change (left.Holds model valuation ∨ right.Holds model valuation) ↔ _
    rw [il free leftSafe valuation, ir free rightSafe valuation]
    exact disjunction_scope model free (binders left) (binders right) l r
      (el.within free leftSafe.1) (er.within free rightSafe.1) leftSafe.2.2 disjoint valuation
  | @all id body target child ih =>
    obtain ⟨bodySafe, fresh⟩ := rectified_all safe
    change (∀ value, body.Holds model (update valuation id value)) ↔ _
    constructor
    · intro holds other agrees
      apply (ih (id :: free) bodySafe (update valuation id (other id))).mp (holds (other id)) other
      intro queried member
      rcases List.mem_cons.mp member with same | external
      · subst queried; simp [update]
      · have different : queried ≠ id := by intro same; exact fresh (same ▸ external)
        simpa [update, different] using agrees queried external
    · intro holds value
      apply (ih (id :: free) bodySafe (update valuation id value)).mpr
      intro other agrees
      apply holds other
      intro queried external
      have different : queried ≠ id := by intro same; exact fresh (same ▸ external)
      simpa [update, different] using agrees queried (List.mem_cons_of_mem id external)

/-- The same interpretation and full original signature are retained. -/
theorem Erases.universal_closure {D : Type} [Nonempty D] (model : Interpretation D)
    {source target} (erased : Erases source target) (free : List Nat)
    (safe : RectifiedWithin free source) :
    (∀ valuation, source.Holds model valuation) ↔ ∀ valuation, target.Holds model valuation := by
  constructor
  · intro original valuation
    exact (erased.holds_iff model free safe valuation).mp (original valuation)
      valuation (agree_refl free valuation)
  · intro result valuation
    exact (erased.holds_iff model free safe valuation).mpr (fun other _ => result other)

/-- Clause semantics universally closes every clause. This is the existing
    ordered distributive clausifier; there is no new parsing or Rust claim. -/
theorem Erases.clause_models {D : Type} [Nonempty D] (model : Interpretation D)
    {source target} (erased : Erases source target) (free : List Nat)
    (safe : RectifiedWithin free source) :
    target.clauses.Models model ↔ ∀ valuation, source.Holds model valuation := by
  rw [GroundFOF.models_iff_holdsAt]
  simp only [GroundFOF.clauses_holdsAt]
  exact (erased.universal_closure model free safe).symm

end Fang.QuantifiedFOF.BinderRemoval
