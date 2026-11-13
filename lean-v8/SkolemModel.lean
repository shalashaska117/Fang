/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent model-extension boundary, not a Rust Skolemization proof. -/
import QuantifiedFormula

namespace Fang.QuantifiedFOF.Skolem

def TermBelow (limit : Nat) : Term → Prop
  | .var _ => True
  | .app symbol arguments => symbol < limit ∧ ∀ term ∈ arguments, TermBelow limit term

def FormulaBelow (limit : Nat) : Formula → Prop
  | .atom atom => ∀ term ∈ atom.args, TermBelow limit term
  | .truth | .falsity => True
  | .neg body => FormulaBelow limit body
  | .conj left right | .disj left right | .implies left right =>
      FormulaBelow limit left ∧ FormulaBelow limit right
  | .all _ body | .ex _ body => FormulaBelow limit body

def PreservesBelow {D : Type} (limit : Nat) (original extended : Interpretation D) : Prop :=
  (∀ symbol, symbol < limit → ∀ arguments,
    extended.function symbol arguments = original.function symbol arguments) ∧
  (∀ predicate arguments, extended.predicate predicate arguments = original.predicate predicate arguments)

theorem term_eval_preserved {D : Type} {limit : Nat} {original extended : Interpretation D}
    (preserves : PreservesBelow limit original extended) (valuation : Nat → D)
    (term : Term) (below : TermBelow limit term) :
    term.eval extended valuation = term.eval original valuation := by
  cases term with
  | var id => simp [Term.eval]
  | app symbol arguments =>
    simp only [TermBelow] at below
    simp only [Term.eval]
    rw [preserves.1 symbol below.1]
    congr 1
    apply List.map_congr_left
    intro term member
    exact term_eval_preserved preserves valuation term (below.2 term member)
termination_by sizeOf term

theorem formula_holds_preserved {D : Type} {limit : Nat} {original extended : Interpretation D}
    (preserves : PreservesBelow limit original extended) (formula : Formula)
    (below : FormulaBelow limit formula) (valuation : Nat → D) :
    formula.Holds extended valuation ↔ formula.Holds original valuation := by
  induction formula generalizing valuation with
  | atom atom =>
    simp only [Formula.Holds, Atom.Holds]
    rw [preserves.2]
    have arguments : atom.args.map (Term.eval extended valuation) =
        atom.args.map (Term.eval original valuation) :=
      List.map_congr_left (fun term member => term_eval_preserved preserves valuation term (below term member))
    rw [arguments]
  | truth | falsity => rfl
  | neg body ih => exact not_congr (ih below valuation)
  | conj left right il ir =>
    simp only [FormulaBelow] at below
    exact and_congr (il below.1 valuation) (ir below.2 valuation)
  | disj left right il ir =>
    simp only [FormulaBelow] at below
    exact or_congr (il below.1 valuation) (ir below.2 valuation)
  | implies left right il ir =>
    simp only [FormulaBelow] at below
    exact imp_congr (il below.1 valuation) (ir below.2 valuation)
  | all id body ih => exact forall_congr' (fun value => ih below (update valuation id value))
  | ex id body ih => exact exists_congr (fun value => ih below (update valuation id value))

/-- A total first-order interpretation assigns the proposed witness to this new
    symbol on argument lists of its declared arity. Other symbols are unchanged. -/
def extendFunction {D : Type} (original : Interpretation D) (fresh arity : Nat)
    (witness : List D → D) : Interpretation D where
  function symbol arguments :=
    if symbol = fresh ∧ arguments.length = arity then witness arguments
    else original.function symbol arguments
  predicate := original.predicate

theorem extendFunction_preserves {D : Type} (original : Interpretation D)
    (fresh arity : Nat) (witness : List D → D) :
    PreservesBelow fresh original (extendFunction original fresh arity witness) := by
  constructor
  · intro symbol below arguments
    have different : symbol ≠ fresh := by omega
    simp [extendFunction, different]
  · intro predicate arguments
    rfl

theorem fresh_application_eval {D : Type} (original : Interpretation D) (fresh : Nat)
    (universals : List Nat) (witness : List D → D) (valuation : Nat → D) :
    (Term.app fresh (universals.map Term.var)).eval
      (extendFunction original fresh universals.length witness) valuation =
        witness (universals.map valuation) := by
  simp [Term.eval, List.map_map, extendFunction, Function.comp_def]

/-- This finite-symbol construction includes the actual ordered argument tuple.
    Its premise is a witness for every tuple of the declared arity. Connecting
    that premise to a quantified body and substitution is a separate obligation. -/
theorem single_symbol_extension {D : Type} [Nonempty D]
    (original : Interpretation D) (fresh : Nat) (universals : List Nat)
    (relation : List D → D → Prop)
    (witnesses : ∀ arguments, arguments.length = universals.length →
      ∃ value, relation arguments value) :
    ∃ extended : Interpretation D,
      PreservesBelow fresh original extended ∧
      ∀ valuation : Nat → D, relation (universals.map valuation)
        ((Term.app fresh (universals.map Term.var)).eval extended valuation) := by
  classical
  let witness : List D → D := fun arguments =>
    if length : arguments.length = universals.length then
      Classical.choose (witnesses arguments length)
    else Classical.choice ‹Nonempty D›
  refine ⟨extendFunction original fresh universals.length witness,
    extendFunction_preserves original fresh universals.length witness, ?_⟩
  intro valuation
  rw [fresh_application_eval]
  simp only [witness, List.length_map, dite_true]
  exact Classical.choose_spec (witnesses (universals.map valuation) (List.length_map ..))

/-- The whole original inventory can contain symbols from later declarations. -/
theorem single_symbol_preserves_problem {D : Type} (original : Interpretation D)
    (fresh arity : Nat) (witness : List D → D) (problem : List Formula)
    (reserved : ∀ formula ∈ problem, FormulaBelow fresh formula) (valuation : Nat → D) :
    (∀ formula ∈ problem, formula.Holds (extendFunction original fresh arity witness) valuation) ↔
      ∀ formula ∈ problem, formula.Holds original valuation := by
  apply forall_congr'
  intro formula
  apply forall_congr'
  intro member
  exact formula_holds_preserved (extendFunction_preserves original fresh arity witness)
    formula (reserved formula member) valuation

end Fang.QuantifiedFOF.Skolem
