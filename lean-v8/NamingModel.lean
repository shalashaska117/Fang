/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Model extension for definitional clausification, over the checker's
   quantifier-free formulas. A definition is a formula `~p(x) | body` whose
   arguments `x` are vars covering those of the body and whose body uses
   only predicates below `p`. Interpreting each defined predicate, in order, as
   the truth of its body turns any interpretation into one where every
   definition holds and every predicate below the first defined one keeps its
   meaning. Nothing here refers to generated code. -/
import BinderSemantics

namespace FangNaming
open Fang Fang.GroundFOF Fang.QuantifiedFOF Fang.QuantifiedFOF.BinderRemoval

theorem snocInduction {α : Type} {motive : List α → Prop} (nil : motive [])
    (step : ∀ first last, motive first → motive (first ++ [last])) (list : List α) : motive list := by
  rw [← List.reverse_reverse list]
  induction list.reverse with
  | nil => exact nil
  | cons head tail ih => rw [List.reverse_cons]; exact step _ head ih

/-- Every predicate of the formula is below `bound`. -/
def PredsBelow (bound : Nat) : GroundFOF.Nnf → Prop
  | .lit literal => literal.atom.pred < bound
  | .truth | .falsity => True
  | .conj left right | .disj left right => PredsBelow bound left ∧ PredsBelow bound right

theorem predsBelow_mono {small large : Nat} (le : small ≤ large) :
    ∀ formula, PredsBelow small formula → PredsBelow large formula
  | .lit _, below => Nat.lt_of_lt_of_le below le
  | .truth, _ | .falsity, _ => trivial
  | .conj left right, below | .disj left right, below =>
    ⟨predsBelow_mono le left below.1, predsBelow_mono le right below.2⟩

/-- The same functions, and the same predicates below `bound`. -/
def AgreeBelow {D : Type} (bound : Nat) (first second : Interpretation D) : Prop :=
  first.function = second.function ∧ ∀ q < bound, first.predicate q = second.predicate q

theorem agreeBelow_refl {D : Type} (bound : Nat) (model : Interpretation D) : AgreeBelow bound model model :=
  ⟨rfl, fun _ _ => rfl⟩

theorem agreeBelow_symm {D : Type} {bound : Nat} {first second : Interpretation D}
    (agree : AgreeBelow bound first second) : AgreeBelow bound second first :=
  ⟨agree.1.symm, fun q below => (agree.2 q below).symm⟩

theorem agreeBelow_trans {D : Type} {bound : Nat} {first second third : Interpretation D}
    (one : AgreeBelow bound first second) (two : AgreeBelow bound second third) : AgreeBelow bound first third :=
  ⟨one.1.trans two.1, fun q below => (one.2 q below).trans (two.2 q below)⟩

theorem agreeBelow_mono {D : Type} {small large : Nat} {first second : Interpretation D}
    (le : small ≤ large) (agree : AgreeBelow large first second) : AgreeBelow small first second :=
  ⟨agree.1, fun q below => agree.2 q (Nat.lt_of_lt_of_le below le)⟩

theorem eval_functions {D : Type} {first second : Interpretation D} (same : first.function = second.function)
    (valuation : Nat → D) : ∀ term : Term, term.eval first valuation = term.eval second valuation
  | .var _ => by simp only [Term.eval]
  | .app symbol arguments => by
    simp only [Term.eval, same]
    congr 1
    exact List.map_congr_left (fun term _ => eval_functions same valuation term)

theorem holds_agreeBelow {D : Type} {bound : Nat} {first second : Interpretation D}
    (agree : AgreeBelow bound first second) (valuation : Nat → D) :
    ∀ formula, PredsBelow bound formula → (formula.Holds first valuation ↔ formula.Holds second valuation)
  | .lit literal, below => by
    have arguments : literal.atom.args.map (Term.eval first valuation) =
        literal.atom.args.map (Term.eval second valuation) :=
      List.map_congr_left (fun term _ => eval_functions agree.1 valuation term)
    simp only [GroundFOF.Nnf.Holds, Literal.Holds, Atom.Holds, arguments, agree.2 _ below]
  | .truth, _ | .falsity, _ => Iff.rfl
  | .conj left right, below =>
    and_congr (holds_agreeBelow agree valuation left below.1) (holds_agreeBelow agree valuation right below.2)
  | .disj left right, below =>
    or_congr (holds_agreeBelow agree valuation left below.1) (holds_agreeBelow agree valuation right below.2)

/-- The valuation that reads the value of variable `x` from the position of
    `x` among the arguments, and an arbitrary value elsewhere. -/
noncomputable def valuationOf {D : Type} [Nonempty D] (arguments : List Term) (values : List D) : Nat → D :=
  fun x => match arguments.findIdx? (fun term => decide (term = .var x)) with
    | some index => values.getD index (Classical.choice inferInstance)
    | none => Classical.choice inferInstance

theorem valuationOf_agree {D : Type} [Nonempty D] (model : Interpretation D) (vars : List Nat)
    (valuation : Nat → D) :
    Agree vars (valuationOf (vars.map Term.var) ((vars.map Term.var).map (Term.eval model valuation)))
      valuation := by
  intro x member
  unfold valuationOf
  have found : ((vars.map Term.var).findIdx? (fun term => decide (term = .var x))).isSome := by
    rw [List.findIdx?_isSome]
    exact List.any_eq_true.mpr ⟨.var x, List.mem_map_of_mem member, by simp⟩
  obtain ⟨index, equation⟩ := Option.isSome_iff_exists.mp found
  rw [equation]
  obtain ⟨bound, hit, _⟩ := List.findIdx?_eq_some_iff_getElem.mp equation
  simp only [decide_eq_true_eq] at hit
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem bound, Option.map_some,
    Option.getD_some, hit, Term.eval]

/-- Interpret the guarded predicate of one definition as the truth of its body. -/
noncomputable def extendOne {D : Type} [Nonempty D] (model : Interpretation D) : GroundFOF.Nnf → Interpretation D
  | .disj (.lit ⟨false, ⟨predicate, arguments⟩⟩) body =>
    { function := model.function,
      predicate := fun q values =>
        if q = predicate then body.Holds model (valuationOf arguments values) else model.predicate q values }
  | _ => model

noncomputable def extend {D : Type} [Nonempty D] (model : Interpretation D)
    (definitions : List GroundFOF.Nnf) : Interpretation D :=
  definitions.foldl extendOne model

theorem extend_append {D : Type} [Nonempty D] (model : Interpretation D) (first second : List GroundFOF.Nnf) :
    extend model (first ++ second) = extend (extend model first) second := by
  simp only [extend, List.foldl_append]

theorem extend_nil {D : Type} [Nonempty D] (model : Interpretation D) : extend model [] = model := rfl

theorem extend_snoc {D : Type} [Nonempty D] (model : Interpretation D) (first : List GroundFOF.Nnf)
    (last : GroundFOF.Nnf) : extend model (first ++ [last]) = extendOne (extend model first) last := by
  simp only [extend, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- One definition of predicate `predicate`. -/
def Definition (predicate : Nat) (formula : GroundFOF.Nnf) : Prop :=
  ∃ (vars : List Nat) (body : GroundFOF.Nnf),
    formula = .disj (.lit ⟨false, ⟨predicate, vars.map Term.var⟩⟩) body ∧
      GroundWithin vars body ∧ PredsBelow predicate body

/-- Definition `j` of the list defines predicate `base + j`. -/
def Definitions (base : Nat) (definitions : List GroundFOF.Nnf) : Prop :=
  ∀ j (h : j < definitions.length), Definition (base + j) definitions[j]

theorem definitions_nil (base : Nat) : Definitions base [] := fun _ h => absurd h (Nat.not_lt_zero _)

theorem definitions_append {base : Nat} {first second : List GroundFOF.Nnf} :
    Definitions base (first ++ second) ↔ Definitions base first ∧ Definitions (base + first.length) second := by
  constructor
  · intro all
    refine ⟨fun j h => ?_, fun j h => ?_⟩
    · have := all j (by simp; omega)
      rwa [List.getElem_append_left h] at this
    · have := all (first.length + j) (by simp; omega)
      rw [List.getElem_append_right (by omega)] at this
      simpa [Nat.add_assoc] using this
  · rintro ⟨one, two⟩ j h
    by_cases left : j < first.length
    · rw [List.getElem_append_left left]
      exact one j left
    · rw [List.getElem_append_right (by omega)]
      have := two (j - first.length) (by simp at h; omega)
      have index : base + first.length + (j - first.length) = base + j := by omega
      rwa [index] at this

theorem definitions_singleton {base : Nat} {formula : GroundFOF.Nnf} :
    Definitions base [formula] ↔ Definition base formula := by
  constructor
  · intro all
    simpa using all 0 (by simp)
  · intro one j h
    have : j = 0 := by simp at h; omega
    subst this
    simpa using one

theorem extendOne_agree {D : Type} [Nonempty D] {predicate : Nat} {formula : GroundFOF.Nnf}
    (definition : Definition predicate formula) (model : Interpretation D) :
    AgreeBelow predicate model (extendOne model formula) := by
  obtain ⟨vars, body, rfl, _, _⟩ := definition
  refine ⟨rfl, fun q below => ?_⟩
  funext values
  simp [extendOne, Nat.ne_of_lt below]

theorem extend_agree {D : Type} [Nonempty D] (model : Interpretation D) :
    ∀ {base : Nat} {definitions : List GroundFOF.Nnf}, Definitions base definitions →
      AgreeBelow base model (extend model definitions) := by
  intro base definitions
  induction definitions using snocInduction with
  | nil => intro _; exact agreeBelow_refl base model
  | step first last ih =>
    intro valid
    obtain ⟨one, two⟩ := definitions_append.mp valid
    rw [extend_snoc]
    exact agreeBelow_trans (ih one) (agreeBelow_mono (Nat.le_add_right _ _)
      (extendOne_agree (definitions_singleton.mp two) _))

theorem extend_append_agree {D : Type} [Nonempty D] (model : Interpretation D) {base : Nat}
    {first second : List GroundFOF.Nnf} (valid : Definitions base (first ++ second)) :
    AgreeBelow (base + first.length) (extend model first) (extend model (first ++ second)) := by
  rw [extend_append]
  exact extend_agree _ (definitions_append.mp valid).2

/-- The atom of a definition holds exactly when its body holds before the definition. -/
theorem extendOne_atom {D : Type} [Nonempty D] (model : Interpretation D) (predicate : Nat)
    (vars : List Nat) (body : GroundFOF.Nnf) (within : GroundWithin vars body)
    (valuation : Nat → D) :
    (GroundFOF.Nnf.lit ⟨true, ⟨predicate, vars.map Term.var⟩⟩).Holds
        (extendOne model (.disj (.lit ⟨false, ⟨predicate, vars.map Term.var⟩⟩) body)) valuation ↔
      body.Holds model valuation := by
  have arguments : (vars.map Term.var).map (Term.eval (extendOne model
      (.disj (.lit ⟨false, ⟨predicate, vars.map Term.var⟩⟩) body)) valuation) =
      (vars.map Term.var).map (Term.eval model valuation) :=
    List.map_congr_left (fun term _ => eval_functions (second := model) (by simp only [extendOne]) valuation term)
  simp only [GroundFOF.Nnf.Holds, Literal.Holds, Atom.Holds, ite_true]
  rw [arguments]
  simp only [extendOne, ite_true]
  exact ground_holds_congr model vars body within _ valuation (valuationOf_agree model vars valuation)

/-- Every definition of a well-formed list holds in the extended interpretation. -/
theorem extend_definitions_hold {D : Type} [Nonempty D] (model : Interpretation D) :
    ∀ {base : Nat} {definitions : List GroundFOF.Nnf}, Definitions base definitions →
      ∀ formula ∈ definitions, ∀ valuation, formula.Holds (extend model definitions) valuation := by
  intro base definitions
  induction definitions using snocInduction with
  | nil => intro _ _ member; cases member
  | step first last ih =>
    intro valid formula member valuation
    obtain ⟨one, two⟩ := definitions_append.mp valid
    have definition := definitions_singleton.mp two
    have agree := extendOne_agree definition (extend model first)
    rw [extend_snoc]
    rcases List.mem_append.mp member with earlier | latest
    · -- An earlier definition uses only predicates below the latest one.
      have below : PredsBelow (base + first.length) formula := by
        obtain ⟨j, h, rfl⟩ := List.getElem_of_mem earlier
        obtain ⟨vars, body, equation, _, bodyBelow⟩ := one j h
        rw [equation]
        exact ⟨show base + j < base + first.length by omega, predsBelow_mono (by omega) body bodyBelow⟩
      exact (holds_agreeBelow agree valuation formula below).mp (ih one formula earlier valuation)
    · rw [List.mem_singleton] at latest
      subst latest
      obtain ⟨vars, body, equation, within, bodyBelow⟩ := definition
      subst equation
      have atom := extendOne_atom (extend model first) (base + first.length) vars body within valuation
      have same := holds_agreeBelow agree valuation body bodyBelow
      simp only [GroundFOF.Nnf.Holds, Literal.Holds] at atom ⊢
      by_cases hit : body.Holds (extend model first) valuation
      · exact Or.inr (same.mp hit)
      · left
        intro holds
        exact hit (atom.mp holds)

end FangNaming
