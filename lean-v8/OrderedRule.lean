/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Ordered positional paramodulation; no search, MGU or byte-parser claim. -/
import OrderedPath
import ClauseUpdate
import Renaming

namespace Fang.Equality.Ordered

structure Witness where
  sourcePivot : Nat
  targetLiteral : Nat
  root : Root
  path : List Nat
  reverse : Bool
  substitution : Subst
  deriving Repr

/-- Both parents are instantiated once by the same simultaneous substitution.
    Numeric root/path selection happens in that instantiated target. -/
def checkRule (source target : Clause) (witness : Witness) : Option Clause := do
  let sourceInstance := source.map (Literal.subst witness.substitution)
  let targetInstance := target.map (Literal.subst witness.substitution)
  let pivot ← sourceInstance[witness.sourcePivot]?
  if pivot.positive then
    match pivot.atom with
    | .predicate _ => none
    | .equal left right =>
      let targetLiteral ← targetInstance[witness.targetLiteral]?
      let (selected, context) ← focusLiteral targetLiteral witness.root witness.path
      if selected = (if witness.reverse then right else left) then
        some (sourceInstance.eraseIdx witness.sourcePivot ++ targetInstance.set witness.targetLiteral
          (context.plug (if witness.reverse then left else right)))
      else none
  else none

def Reconstruction (source target : Clause) (witness : Witness) (output : Clause) : Prop :=
  let sourceInstance := source.map (Literal.subst witness.substitution)
  let targetInstance := target.map (Literal.subst witness.substitution)
  ∃ left right selected context,
    sourceInstance[witness.sourcePivot]? = some ⟨true, .equal left right⟩ ∧
    targetInstance[witness.targetLiteral]? = some selected ∧
    focusLiteral selected witness.root witness.path = some ((if witness.reverse then right else left), context) ∧
    output = sourceInstance.eraseIdx witness.sourcePivot ++ targetInstance.set witness.targetLiteral
      (context.plug (if witness.reverse then left else right))

theorem checkRule_iff (source target output : Clause) (witness : Witness) :
    checkRule source target witness = some output ↔ Reconstruction source target witness output := by
  constructor
  · intro accepted
    cases pivotAt : (source.map (Literal.subst witness.substitution))[witness.sourcePivot]? with
    | none => simp [checkRule, pivotAt] at accepted
    | some pivot =>
      cases pivot with
      | mk positive atom =>
        cases positive with
        | false => simp [checkRule, pivotAt] at accepted
        | true =>
          cases atom with
          | predicate atom => simp [checkRule, pivotAt] at accepted
          | equal left right =>
            cases targetAt : (target.map (Literal.subst witness.substitution))[witness.targetLiteral]? with
            | none => simp [checkRule, pivotAt, targetAt] at accepted
            | some selectedLiteral =>
              cases focus : focusLiteral selectedLiteral witness.root witness.path with
              | none => simp [checkRule, pivotAt, targetAt, focus] at accepted
              | some value =>
                rcases value with ⟨selected, context⟩
                simp only [checkRule, pivotAt, targetAt, focus, bind, Option.bind, ite_eq_left] at accepted
                by_cases matched : selected = (if witness.reverse then right else left)
                · simp only [matched, ite_eq_left] at accepted
                  exact ⟨left, right, selectedLiteral, context, pivotAt, targetAt,
                    by simpa only [matched] using focus, (Option.some.inj accepted).symm⟩
                · simp only [ite_eq_right matched] at accepted
                  contradiction
  · rintro ⟨left, right, selected, context, pivotAt, targetAt, focus, outputEq⟩
    rw [outputEq]
    simp [checkRule, pivotAt, targetAt, focus]

theorem checkRule_sound {D : Type} (model : Interpretation D) (source target output : Clause)
    (witness : Witness) (sourceValid : clauseValid model source) (targetValid : clauseValid model target)
    (accepted : checkRule source target witness = some output) : clauseValid model output := by
  obtain ⟨left, right, selected, context, pivotAt, targetAt, focus, outputEq⟩ :=
    (checkRule_iff source target output witness).mp accepted
  have sourceInstance := clause_valid_subst model witness.substitution source sourceValid
  have targetInstance := clause_valid_subst model witness.substitution target targetValid
  intro valuation
  rw [outputEq]
  apply FangParamodulation.ordered_update_consequence (fun (literal : Literal) => literal.Holds model valuation)
    (source.map (Literal.subst witness.substitution)) (target.map (Literal.subst witness.substitution))
    witness.sourcePivot witness.targetLiteral ⟨true, .equal left right⟩ selected
    (context.plug (if witness.reverse then left else right)) pivotAt targetAt
    (by simpa only [clauseHolds] using sourceInstance valuation)
    (by simpa only [clauseHolds] using targetInstance valuation)
  intro equalityHolds selectedHolds
  have forward : left.eval model valuation = right.eval model valuation := by
    simpa only [Literal.Holds, Bool.true_eq, ite_eq_left, Atom.Holds] using equalityHolds
  have oriented : (if witness.reverse then right else left).eval model valuation =
      (if witness.reverse then left else right).eval model valuation := by
    cases witness.reverse <;> simp_all
  rw [← focusLiteral_plug selected witness.root witness.path _ context focus] at selectedHolds
  exact (literal_context_congruence model valuation context _ _ oriented).mp selectedHolds

/-- A trace node always uses disjoint even/odd original parent namespaces.
    Supplying the same parent ID twice remains well-defined. -/
def infer (source target : Clause) (witness : Witness) : Option Clause :=
  checkRule (source.map (Literal.rename Fang.leftRename))
    (target.map (Literal.rename Fang.rightRename)) witness

theorem infer_sound {D : Type} (model : Interpretation D) (source target output : Clause)
    (witness : Witness) (sourceValid : clauseValid model source) (targetValid : clauseValid model target)
    (accepted : infer source target witness = some output) : clauseValid model output :=
  checkRule_sound model _ _ output witness
    (clause_valid_rename model Fang.leftRename source sourceValid)
    (clause_valid_rename model Fang.rightRename target targetValid) accepted

end Fang.Equality.Ordered
