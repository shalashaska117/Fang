/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Substitution

namespace Fang.QuantifiedFOF.Skolem

theorem term_within_eval_congr {D : Type} (model : Interpretation D) (bound : List Nat)
    (term : Term) (within : TermWithin bound term) (left right : Nat → D)
    (agree : ∀ id ∈ bound, left id = right id) : term.eval model left = term.eval model right := by
  cases term with
  | var id =>
    simp only [TermWithin] at within
    simpa [Term.eval] using agree id within
  | app symbol arguments =>
    simp only [TermWithin] at within
    simp only [Term.eval]
    congr 1
    apply List.map_congr_left
    intro term member
    exact term_within_eval_congr model bound term (within term member) left right agree
termination_by sizeOf term

theorem formula_within_holds_congr {D : Type} (model : Interpretation D) (bound : List Nat)
    (formula : Formula) (within : formula.Within bound) (left right : Nat → D)
    (agree : ∀ id ∈ bound, left id = right id) : formula.Holds model left ↔ formula.Holds model right := by
  induction formula generalizing bound left right with
  | atom atom =>
    simp only [Formula.Holds, Atom.Holds]
    have arguments : atom.args.map (Term.eval model left) = atom.args.map (Term.eval model right) :=
      List.map_congr_left (fun term member => term_within_eval_congr model bound term (within term member) left right agree)
    rw [arguments]
  | truth | falsity => rfl
  | neg body ih => exact not_congr (ih bound within left right agree)
  | conj l r il ir | disj l r il ir | implies l r il ir =>
    simp only [Formula.Within] at within
    first
    | exact and_congr (il bound within.1 left right agree) (ir bound within.2 left right agree)
    | exact or_congr (il bound within.1 left right agree) (ir bound within.2 left right agree)
    | exact imp_congr (il bound within.1 left right agree) (ir bound within.2 left right agree)
  | all id body ih | ex id body ih =>
    have each (value : D) := ih (id :: bound) within (update left id value) (update right id value)
    have agreeing (value : D) : ∀ queried ∈ id :: bound,
        update left id value queried = update right id value queried := by
      intro queried member
      by_cases same : queried = id
      · simp [update, same]
      · have rest : queried ∈ bound := (List.mem_cons.mp member).resolve_left same
        simpa [update, same] using agree queried rest
    first
    | exact forall_congr' (fun value => each value (agreeing value))
    | exact exists_congr (fun value => each value (agreeing value))

/-- The first occurrence determines a position. The reconstruction theorem below
    needs only tuples produced from a valuation; duplicate IDs then agree. -/
def tupleValuation {D : Type} (fallback : D) : List Nat → List D → Nat → D
  | id :: ids, value :: values => update (tupleValuation fallback ids values) id value
  | _, _ => fun _ => fallback

theorem tupleValuation_mapped {D : Type} (fallback : D) (ids : List Nat)
    (valuation : Nat → D) (queried : Nat) (member : queried ∈ ids) :
    tupleValuation fallback ids (ids.map valuation) queried = valuation queried := by
  induction ids with
  | nil => cases member
  | cons id ids ih =>
    by_cases same : queried = id
    · simp [tupleValuation, update, same]
    · have rest : queried ∈ ids := (List.mem_cons.mp member).resolve_left same
      simpa [tupleValuation, update, same] using ih rest

theorem body_tuple_holds {D : Type} (model : Interpretation D) (fallback : D)
    (universals : List Nat) (binder : Nat) (body : Formula)
    (within : body.Within (binder :: universals)) (valuation : Nat → D) (value : D) :
    body.Holds model (update (tupleValuation fallback universals (universals.map valuation)) binder value) ↔
      body.Holds model (update valuation binder value) := by
  apply formula_within_holds_congr model (binder :: universals) body within
  intro queried member
  by_cases same : queried = binder
  · simp [update, same]
  · have rest : queried ∈ universals := (List.mem_cons.mp member).resolve_left same
    simpa [update, same] using tupleValuation_mapped fallback universals valuation queried rest

/-- A witness is needed only when the existential body is satisfiable at this
    tuple. The fallback supplies a value for unused or impossible instances. -/
theorem body_tuple_witness {D : Type} [Nonempty D] (model : Interpretation D)
    (fallback : D) (universals : List Nat) (binder : Nat) (body : Formula) (arguments : List D) :
    ∃ value, (∃ candidate, body.Holds model
      (update (tupleValuation fallback universals arguments) binder candidate)) →
      body.Holds model (update (tupleValuation fallback universals arguments) binder value) := by
  classical
  by_cases possible : ∃ candidate, body.Holds model
      (update (tupleValuation fallback universals arguments) binder candidate)
  · exact ⟨Classical.choose possible, fun _ => Classical.choose_spec possible⟩
  · exact ⟨fallback, fun contradiction => False.elim (possible contradiction)⟩

end Fang.QuantifiedFOF.Skolem
