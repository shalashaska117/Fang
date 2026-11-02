/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent certificate semantics. This is not a generated Rust model. -/
import Fang.Logic

namespace Fang.Equality

inductive Atom where
  | predicate : Fang.Atom → Atom
  | equal : Term → Term → Atom
  deriving DecidableEq, Repr

structure Literal where
  positive : Bool
  atom : Atom
  deriving DecidableEq, Repr

abbrev Clause := List Literal

def Atom.Holds {D : Type} (model : Interpretation D) (valuation : Nat → D) : Atom → Prop
  | .predicate atom => atom.Holds model valuation
  | .equal left right => left.eval model valuation = right.eval model valuation

def Literal.Holds {D : Type} (model : Interpretation D) (valuation : Nat → D) (literal : Literal) : Prop :=
  if literal.positive then literal.atom.Holds model valuation else ¬ literal.atom.Holds model valuation

def clauseHolds {D : Type} (model : Interpretation D) (valuation : Nat → D) (clause : Clause) : Prop :=
  ∃ literal ∈ clause, literal.Holds model valuation

def clauseValid {D : Type} (model : Interpretation D) (clause : Clause) : Prop :=
  ∀ valuation, clauseHolds model valuation clause

def Atom.subst (substitution : Subst) : Atom → Atom
  | .predicate atom => .predicate (atom.subst substitution)
  | .equal left right => .equal (left.subst substitution) (right.subst substitution)

def Literal.subst (substitution : Subst) (literal : Literal) : Literal :=
  ⟨literal.positive, literal.atom.subst substitution⟩

theorem atom_holds_subst {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (substitution : Subst) (atom : Atom) :
    (atom.subst substitution).Holds model valuation ↔
      atom.Holds model (fun varId => (lookup substitution varId).eval model valuation) := by
  cases atom <;>
    simp [Atom.subst, Atom.Holds, Fang.Atom.subst, Fang.Atom.Holds,
      List.map_map, Function.comp_def, Term.eval_subst]

theorem literal_holds_subst {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (substitution : Subst) (literal : Literal) :
    (literal.subst substitution).Holds model valuation ↔
      literal.Holds model (fun varId => (lookup substitution varId).eval model valuation) := by
  simp [Literal.subst, Literal.Holds, atom_holds_subst]

theorem clause_valid_subst {D : Type} (model : Interpretation D) (substitution : Subst)
    (clause : Clause) (valid : clauseValid model clause) :
    clauseValid model (clause.map (Literal.subst substitution)) := by
  intro valuation
  obtain ⟨literal, member, holds⟩ := valid (fun varId => (lookup substitution varId).eval model valuation)
  exact ⟨literal.subst substitution, List.mem_map.mpr ⟨literal, member, rfl⟩,
    (literal_holds_subst model valuation substitution literal).mpr holds⟩

theorem clause_cons_holds {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (literal : Literal) (rest : Clause) :
    clauseHolds model valuation (literal :: rest) ↔ literal.Holds model valuation ∨ clauseHolds model valuation rest := by
  simp [clauseHolds, or_and_right, exists_or]

theorem clause_append_holds {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (left right : Clause) :
    clauseHolds model valuation (left ++ right) ↔ clauseHolds model valuation left ∨ clauseHolds model valuation right := by
  simp [clauseHolds, or_and_right, exists_or]

/-- A finite substitution witness need only equalize the selected terms; MGU status is separate. -/
theorem equality_resolution_sound {D : Type} (model : Interpretation D)
    (left right : Term) (rest : Clause) (substitution : Subst)
    (premise : clauseValid model (⟨false, .equal left right⟩ :: rest))
    (equalized : left.subst substitution = right.subst substitution) :
    clauseValid model (rest.map (Literal.subst substitution)) := by
  intro valuation
  have instantiated := clause_valid_subst model substitution _ premise valuation
  rw [List.map_cons, clause_cons_holds] at instantiated
  rcases instantiated with impossible | remainder
  · simp [Literal.subst, Atom.subst, Literal.Holds, Atom.Holds, equalized] at impossible
  · exact remainder

/-- One chosen occurrence, including a whole term. Fixed siblings preserve argument order. -/
inductive TermContext where
  | hole : TermContext
  | app : Nat → List Term → TermContext → List Term → TermContext
  deriving Repr

def TermContext.plug : TermContext → Term → Term
  | .hole, term => term
  | .app symbol before inner after, term => .app symbol (before ++ inner.plug term :: after)

theorem term_context_congruence {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (context : TermContext) (left right : Term)
    (same : left.eval model valuation = right.eval model valuation) :
    (context.plug left).eval model valuation = (context.plug right).eval model valuation := by
  induction context with
  | hole => exact same
  | app symbol before inner after ih => simp [TermContext.plug, Term.eval, ih]

inductive LiteralContext where
  | predicate : Bool → Nat → List Term → TermContext → List Term → LiteralContext
  | equalityLeft : Bool → TermContext → Term → LiteralContext
  | equalityRight : Bool → Term → TermContext → LiteralContext
  deriving Repr

def LiteralContext.plug : LiteralContext → Term → Literal
  | .predicate positive symbol before inner after, term =>
      ⟨positive, .predicate ⟨symbol, before ++ inner.plug term :: after⟩⟩
  | .equalityLeft positive inner other, term => ⟨positive, .equal (inner.plug term) other⟩
  | .equalityRight positive other inner, term => ⟨positive, .equal other (inner.plug term)⟩

theorem literal_context_congruence {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (context : LiteralContext) (left right : Term)
    (same : left.eval model valuation = right.eval model valuation) :
    (context.plug left).Holds model valuation ↔ (context.plug right).Holds model valuation := by
  cases context with
  | predicate positive symbol before inner after =>
    simp [LiteralContext.plug, Literal.Holds, Atom.Holds, Fang.Atom.Holds,
      term_context_congruence model valuation inner left right same]
  | equalityLeft positive inner other =>
    simp [LiteralContext.plug, Literal.Holds, Atom.Holds,
      term_context_congruence model valuation inner left right same] <;> rfl
  | equalityRight positive other inner =>
    simp [LiteralContext.plug, Literal.Holds, Atom.Holds,
      term_context_congruence model valuation inner left right same] <;> rfl

/-- Sound unrestricted paramodulation; ordering and selection restrict search, not this implication. -/
theorem paramodulation_sound {D : Type} (model : Interpretation D)
    (left right : Term) (equalityRest : Clause) (target : Literal) (targetRest : Clause)
    (substitution : Subst) (context : LiteralContext)
    (equalityPremise : clauseValid model (⟨true, .equal left right⟩ :: equalityRest))
    (targetPremise : clauseValid model (target :: targetRest))
    (matched : target.subst substitution = context.plug (left.subst substitution)) :
    clauseValid model (context.plug (right.subst substitution) ::
      (equalityRest.map (Literal.subst substitution) ++ targetRest.map (Literal.subst substitution))) := by
  intro valuation
  have equalityInstance := clause_valid_subst model substitution _ equalityPremise valuation
  have targetInstance := clause_valid_subst model substitution _ targetPremise valuation
  rw [List.map_cons, clause_cons_holds] at equalityInstance targetInstance
  rw [clause_cons_holds, clause_append_holds]
  rcases equalityInstance with equal | equalityRemainder
  · rcases targetInstance with targetHolds | targetRemainder
    · left
      rw [matched] at targetHolds
      apply (literal_context_congruence model valuation context _ _ ?_).mp targetHolds
      simpa [Literal.subst, Atom.subst, Literal.Holds, Atom.Holds] using equal
    · exact Or.inr (Or.inr targetRemainder)
  · exact Or.inr (Or.inl equalityRemainder)

/-- Explicit before/after witnesses preserve all unselected literals and their order. -/
def checkEqualityResolution (premise before after : Clause) (left right : Term)
    (substitution : Subst) : Option Clause :=
  if premise = before ++ ⟨false, .equal left right⟩ :: after ∧
      left.subst substitution = right.subst substitution then
    some ((before ++ after).map (Literal.subst substitution))
  else none

theorem checkEqualityResolution_sound {D : Type} (model : Interpretation D)
    (premise before after output : Clause) (left right : Term) (substitution : Subst)
    (valid : clauseValid model premise)
    (accepted : checkEqualityResolution premise before after left right substitution = some output) :
    clauseValid model output := by
  unfold checkEqualityResolution at accepted
  split at accepted
  next checked =>
    cases accepted
    apply equality_resolution_sound model left right (before ++ after) substitution _ checked.2
    intro valuation
    have original := valid valuation
    rw [checked.1, clause_append_holds, clause_cons_holds] at original
    rw [clause_cons_holds, clause_append_holds]
    rcases original with prefixHolds | pivotHolds | suffixHolds
    · exact Or.inr (Or.inl prefixHolds)
    · exact Or.inl pivotHolds
    · exact Or.inr (Or.inr suffixHolds)
  next rejected => contradiction

theorem focus_valid {D : Type} (model : Interpretation D) (before after : Clause) (pivot : Literal)
    (valid : clauseValid model (before ++ pivot :: after)) :
    clauseValid model (pivot :: (before ++ after)) := by
  intro valuation
  have original := valid valuation
  rw [clause_append_holds, clause_cons_holds] at original
  rw [clause_cons_holds, clause_append_holds]
  rcases original with beforeHolds | pivotHolds | afterHolds
  · exact Or.inr (Or.inl beforeHolds)
  · exact Or.inl pivotHolds
  · exact Or.inr (Or.inr afterHolds)

def checkParamodulation (equalityPremise targetPremise equalityBefore equalityAfter targetBefore targetAfter : Clause)
    (left right : Term) (target : Literal) (substitution : Subst) (context : LiteralContext) : Option Clause :=
  if equalityPremise = equalityBefore ++ ⟨true, .equal left right⟩ :: equalityAfter ∧
      targetPremise = targetBefore ++ target :: targetAfter ∧
      target.subst substitution = context.plug (left.subst substitution) then
    some (context.plug (right.subst substitution) ::
      ((equalityBefore ++ equalityAfter).map (Literal.subst substitution) ++
        (targetBefore ++ targetAfter).map (Literal.subst substitution)))
  else none

theorem checkParamodulation_sound {D : Type} (model : Interpretation D)
    (equalityPremise targetPremise equalityBefore equalityAfter targetBefore targetAfter output : Clause)
    (left right : Term) (target : Literal) (substitution : Subst) (context : LiteralContext)
    (equalityValid : clauseValid model equalityPremise) (targetValid : clauseValid model targetPremise)
    (accepted : checkParamodulation equalityPremise targetPremise equalityBefore equalityAfter targetBefore targetAfter
      left right target substitution context = some output) : clauseValid model output := by
  unfold checkParamodulation at accepted
  split at accepted
  next checked =>
    cases accepted
    rw [checked.1] at equalityValid
    rw [checked.2.1] at targetValid
    exact paramodulation_sound model left right (equalityBefore ++ equalityAfter) target
      (targetBefore ++ targetAfter) substitution context
      (focus_valid model equalityBefore equalityAfter _ equalityValid)
      (focus_valid model targetBefore targetAfter target targetValid) checked.2.2
  next rejected => contradiction

end Fang.Equality
