/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   One existential elimination with a fresh function interpretation. -/
import TupleWitness

namespace Fang.QuantifiedFOF.Skolem

/-- The witness depends only on the ordered universal tuple. The scope premise
    must already account for earlier existential replacements. This theorem
    constructs an extension of an original model; it does not say that every
    interpretation of the fresh symbol is a valid extension. -/
theorem existential_extension {D : Type} [Nonempty D] (original : Interpretation D)
    (fresh : Nat) (universals : List Nat) (binder : Nat) (body : Formula)
    (reserved : FormulaBelow fresh body)
    (within : body.Within (binder :: universals))
    (safe : CaptureSafe binder (.app fresh (universals.map Term.var)) body) :
    ∃ extended : Interpretation D, PreservesBelow fresh original extended ∧
      ∀ valuation : Nat → D,
        (Formula.ex binder body).Holds original valuation ↔
        (substitute binder (.app fresh (universals.map Term.var)) body).Holds extended valuation := by
  classical
  let fallback : D := Classical.choice ‹Nonempty D›
  let relation : List D → D → Prop := fun arguments value =>
    (∃ candidate, body.Holds original
      (update (tupleValuation fallback universals arguments) binder candidate)) →
      body.Holds original (update (tupleValuation fallback universals arguments) binder value)
  obtain ⟨extended, preserves, witnesses⟩ := single_symbol_extension original fresh universals relation
    (fun arguments _ => body_tuple_witness original fallback universals binder body arguments)
  refine ⟨extended, preserves, ?_⟩
  intro valuation
  rw [substitute_holds extended valuation binder _ body safe]
  rw [formula_holds_preserved preserves body reserved]
  constructor
  · rintro ⟨value, holds⟩
    have canonical : ∃ candidate, body.Holds original
        (update (tupleValuation fallback universals (universals.map valuation)) binder candidate) :=
      ⟨value, (body_tuple_holds original fallback universals binder body within valuation value).mpr holds⟩
    have chosen := witnesses valuation canonical
    exact (body_tuple_holds original fallback universals binder body within valuation _).mp chosen
  · intro holds
    exact ⟨_, holds⟩

/-- Every original declaration is preserved by the same extension. Reservation
    ranges over the full input, including symbols first used in later clauses. -/
theorem existential_extension_problem {D : Type} [Nonempty D] (original : Interpretation D)
    (fresh : Nat) (universals : List Nat) (binder : Nat) (body : Formula)
    (problem : List Formula) (reserved : FormulaBelow fresh body)
    (problemReserved : ∀ formula ∈ problem, FormulaBelow fresh formula)
    (within : body.Within (binder :: universals))
    (safe : CaptureSafe binder (.app fresh (universals.map Term.var)) body) :
    ∃ extended : Interpretation D, PreservesBelow fresh original extended ∧
      (∀ formula ∈ problem, ∀ valuation, formula.Holds extended valuation ↔ formula.Holds original valuation) ∧
      ∀ valuation : Nat → D,
        (Formula.ex binder body).Holds original valuation ↔
        (substitute binder (.app fresh (universals.map Term.var)) body).Holds extended valuation := by
  obtain ⟨extended, preserves, equivalent⟩ := existential_extension original fresh universals binder body reserved within safe
  exact ⟨extended, preserves,
    fun formula member valuation => formula_holds_preserved preserves formula (problemReserved formula member) valuation,
    equivalent⟩

end Fang.QuantifiedFOF.Skolem
