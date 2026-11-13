/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Capture conditions and semantics for the independent quantified checker model. -/
import SkolemModel

namespace Fang.QuantifiedFOF.Skolem

def TermAvoid (binder : Nat) : Term → Prop
  | .var id => id ≠ binder
  | .app _ arguments => ∀ term ∈ arguments, TermAvoid binder term

def CaptureSafe (binder : Nat) (replacement : Term) : Formula → Prop
  | .atom _ | .truth | .falsity => True
  | .neg body => CaptureSafe binder replacement body
  | .conj left right | .disj left right | .implies left right =>
      CaptureSafe binder replacement left ∧ CaptureSafe binder replacement right
  | .all id body | .ex id body =>
      id = binder ∨ (TermAvoid id replacement ∧ CaptureSafe binder replacement body)

def substitute (binder : Nat) (replacement : Term) : Formula → Formula
  | .atom atom => .atom (atom.subst [(binder, replacement)])
  | .truth => .truth
  | .falsity => .falsity
  | .neg body => .neg (substitute binder replacement body)
  | .conj left right => .conj (substitute binder replacement left) (substitute binder replacement right)
  | .disj left right => .disj (substitute binder replacement left) (substitute binder replacement right)
  | .implies left right => .implies (substitute binder replacement left) (substitute binder replacement right)
  | .all id body => if id = binder then .all id body else .all id (substitute binder replacement body)
  | .ex id body => if id = binder then .ex id body else .ex id (substitute binder replacement body)

theorem update_same {D : Type} (valuation : Nat → D) (id : Nat) (old value : D) :
    update (update valuation id old) id value = update valuation id value := by
  funext queried
  by_cases same : queried = id <;> simp [update, same]

theorem update_commute {D : Type} (valuation : Nat → D) (left right : Nat)
    (leftValue rightValue : D) (different : left ≠ right) :
    update (update valuation left leftValue) right rightValue =
      update (update valuation right rightValue) left leftValue := by
  funext queried
  by_cases l : queried = left <;> by_cases r : queried = right <;> simp_all [update]

theorem term_eval_avoid {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (binder : Nat) (value : D) (term : Term) (avoids : TermAvoid binder term) :
    term.eval model (update valuation binder value) = term.eval model valuation := by
  cases term with
  | var id =>
    simp only [TermAvoid] at avoids
    simp [Term.eval, update, avoids]
  | app symbol arguments =>
    simp only [TermAvoid] at avoids
    simp only [Term.eval]
    congr 1
    apply List.map_congr_left
    intro term member
    exact term_eval_avoid model valuation binder value term (avoids term member)
termination_by sizeOf term

theorem singleton_subst_eval {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (binder : Nat) (replacement term : Term) :
    (term.subst [(binder, replacement)]).eval model valuation =
      term.eval model (update valuation binder (replacement.eval model valuation)) := by
  rw [Term.eval_subst]
  congr 1
  funext queried
  by_cases same : binder = queried
  · subst queried
    simp [lookup, update]
  · have reversed : queried ≠ binder := Ne.symm same
    simp [lookup, update, same, reversed, Term.eval]

/-- Stopping at a rebinding and avoiding all other replacement-variable captures
    are explicit conditions; no alpha-renaming is hidden in this definition. -/
theorem substitute_holds {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (binder : Nat) (replacement : Term) (formula : Formula)
    (safe : CaptureSafe binder replacement formula) :
    (substitute binder replacement formula).Holds model valuation ↔
      formula.Holds model (update valuation binder (replacement.eval model valuation)) := by
  induction formula generalizing valuation with
  | atom atom =>
    simp only [substitute, Formula.Holds, Atom.subst, Atom.Holds, List.map_map]
    have terms : atom.args.map (fun term => (term.subst [(binder, replacement)]).eval model valuation) =
        atom.args.map (fun term => term.eval model (update valuation binder (replacement.eval model valuation))) :=
      List.map_congr_left (fun term _ => singleton_subst_eval model valuation binder replacement term)
    simp only [Function.comp_def, terms]
  | truth | falsity => rfl
  | neg body ih => exact not_congr (ih valuation safe)
  | conj left right il ir | disj left right il ir | implies left right il ir =>
    simp only [CaptureSafe] at safe
    first
    | exact and_congr (il valuation safe.1) (ir valuation safe.2)
    | exact or_congr (il valuation safe.1) (ir valuation safe.2)
    | exact imp_congr (il valuation safe.1) (ir valuation safe.2)
  | all id body ih | ex id body ih =>
    by_cases same : id = binder
    · subst id
      simp [substitute, Formula.Holds, update_same]
    · have allowed := (show id = binder ∨ (TermAvoid id replacement ∧ CaptureSafe binder replacement body) from safe).resolve_left same
      simp only [substitute, same, Formula.Holds]
      have body_equivalent := fun value => ih (update valuation id value) allowed.2
      have each (value : D) :
          (substitute binder replacement body).Holds model (update valuation id value) ↔
          body.Holds model (update (update valuation binder (replacement.eval model valuation)) id value) := by
        rw [body_equivalent value, term_eval_avoid model valuation id value replacement allowed.1]
        rw [update_commute valuation id binder value (replacement.eval model valuation) same]
      first | exact forall_congr' each | exact exists_congr each

end Fang.QuantifiedFOF.Skolem
