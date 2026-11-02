/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent CNF constant normalization; no Rust refinement claim. -/
import FofSyntax

namespace Fang.TptpCandidate.FullFof.BooleanCnf

inductive Literal (α : Type) where
  | ordinary : α → Literal α
  | boolean : Bool → Bool → Literal α
  deriving Repr, DecidableEq

def ordinary : List (Literal α) → List α
  | [] => []
  | .ordinary value :: rest => value :: ordinary rest
  | .boolean _ _ :: rest => ordinary rest

/-- None is a tautology; Some [] is falsity. -/
def normalize : List (Literal α) → Option (List α)
  | [] => some []
  | .ordinary value :: rest => (normalize rest).map (value :: ·)
  | .boolean positive value :: rest =>
    if positive == value then none else normalize rest

def clauseHolds (eval : α → Prop) : List α → Prop
  | [] => False
  | value :: rest => eval value ∨ clauseHolds eval rest

def rawHolds (eval : α → Prop) : List (Literal α) → Prop
  | [] => False
  | .ordinary value :: rest => eval value ∨ rawHolds eval rest
  | .boolean positive value :: rest => positive = value ∨ rawHolds eval rest

def outputHolds (eval : α → Prop) : Option (List α) → Prop
  | none => True
  | some values => clauseHolds eval values

theorem normalize_holds (eval : α → Prop) (values : List (Literal α)) :
    outputHolds eval (normalize values) ↔ rawHolds eval values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    cases value with
    | ordinary value =>
      cases result : normalize rest <;>
        simp_all [normalize, rawHolds, outputHolds, clauseHolds]
    | boolean positive value =>
      cases positive <;> cases value <;> simp_all [normalize, rawHolds, outputHolds]

/-- Surviving clauses keep every ordinary literal in the original order. -/
theorem normalize_some {values : List (Literal α)} {result : List α}
    (success : normalize values = some result) : result = ordinary values := by
  induction values generalizing result with
  | nil => simpa [normalize, ordinary] using success.symm
  | cons value rest ih =>
    cases value with
    | ordinary value =>
      cases tail : normalize rest with
      | none => simp [normalize, tail] at success
      | some more =>
        have same : result = value :: more := by simpa [normalize, tail] using success.symm
        simpa [ordinary, ih tail] using same
    | boolean positive value =>
      by_cases truth : positive = value
      · simp [normalize, truth] at success
      · exact ih (by simpa [normalize, truth] using success)

def blocks (values : List (Literal α)) : List (List α) :=
  match normalize values with | none => [] | some clause => [clause]

theorem blocks_holds (eval : α → Prop) (values : List (Literal α)) :
    (∀ clause ∈ blocks values, clauseHolds eval clause) ↔ rawHolds eval values := by
  rw [← normalize_holds]
  unfold blocks
  cases normalize values <;> simp [outputHolds]

theorem blocks_length (values : List (Literal α)) : (blocks values).length ≤ 1 := by
  unfold blocks
  cases normalize values <;> simp

def formula : List (Literal Formula) → Formula
  | [] => .falsity
  | .ordinary value :: rest => .pair .disj value (formula rest)
  | .boolean positive value :: rest =>
    .pair .disj (if positive = value then .truth else .falsity) (formula rest)

theorem formula_holds {D : Type} (model : Source.Interpretation D) (valuation : String → D)
    (values : List (Literal Formula)) :
    (formula values).Holds model valuation ↔ rawHolds (Formula.Holds model valuation) values := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    cases value with
    | ordinary value => simpa [formula, Formula.Holds, Binary.meaning, rawHolds] using or_congr Iff.rfl ih
    | boolean positive value =>
      cases positive <;> cases value <;>
        simp_all [formula, Formula.Holds, Binary.meaning, rawHolds]

theorem normalized_formula_holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) (values : List (Literal Formula)) :
    outputHolds (Formula.Holds model valuation) (normalize values) ↔
      (formula values).Holds model valuation :=
  (normalize_holds _ _).trans (formula_holds _ _ _).symm

theorem signed_constants :
    normalize ([.boolean true true] : List (Literal Nat)) = none ∧
    normalize ([.boolean true false] : List (Literal Nat)) = some [] ∧
    normalize ([.boolean false true] : List (Literal Nat)) = some [] ∧
    normalize ([.boolean false false] : List (Literal Nat)) = none := by decide

theorem ordered_duplicates :
    normalize ([.ordinary 3, .boolean false true, .ordinary 3] : List (Literal Nat)) =
      some [3, 3] := by decide

theorem ignored_clause_retains_occurrences :
    ordinary ([.boolean true true, .ordinary 3, .ordinary 4] : List (Literal Nat)) = [3, 4] ∧
    blocks ([.boolean true true, .ordinary 3, .ordinary 4] : List (Literal Nat)) = [] := by decide

#print axioms Fang.TptpCandidate.FullFof.BooleanCnf.normalize_holds
#print axioms Fang.TptpCandidate.FullFof.BooleanCnf.normalize_some
#print axioms Fang.TptpCandidate.FullFof.BooleanCnf.blocks_holds
#print axioms Fang.TptpCandidate.FullFof.BooleanCnf.blocks_length
#print axioms Fang.TptpCandidate.FullFof.BooleanCnf.formula_holds
#print axioms Fang.TptpCandidate.FullFof.BooleanCnf.normalized_formula_holds
#print axioms Fang.TptpCandidate.FullFof.BooleanCnf.signed_constants
#print axioms Fang.TptpCandidate.FullFof.BooleanCnf.ordered_duplicates
#print axioms Fang.TptpCandidate.FullFof.BooleanCnf.ignored_clause_retains_occurrences

end Fang.TptpCandidate.FullFof.BooleanCnf
