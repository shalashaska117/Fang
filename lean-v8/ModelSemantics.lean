/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Finite models and a decision procedure for the source semantics over them. A model has the domain `Fin (size + 1)`
   and tables keyed by symbol name and arity. Its interpretation reads cells through the same lookup the evaluator
   uses, so nothing about the tables or the certificate parser is needed: whatever a parser builds is some
   interpretation, and `sentenceValue_iff` decides `∀ valuation, formula.Holds` in it. This module imports no
   extracted code. -/
import FofSyntax
import Std.Data.HashSet

namespace Fang.TptpCandidate.FullFof.Model

/-! Tables and models. -/

/-- The cells of one symbol in row-major order, first argument most significant: every cell, or a default with the
    cells that differ from it. -/
inductive Table where
  | dense : Array Nat → Table
  | sparse : Nat → Std.HashMap Nat Nat → Table

def Table.read : Table → Nat → Nat
  | .dense cells, index => cells.getD index 0
  | .sparse fallback exceptions, index => exceptions.getD index fallback

/-- A structure over the nonempty domain `Fin (size + 1)`. Function and predicate symbols are keyed by name and
    arity, as `Source.Interpretation` takes the argument list. -/
structure FiniteModel where
  size : Nat
  functions : Std.HashMap (String × Nat) Table
  predicates : Std.HashMap (String × Nat) Table

abbrev FiniteModel.Element (model : FiniteModel) : Type := Fin (model.size + 1)

def cellIndex (base : Nat) (arguments : List Nat) : Nat :=
  arguments.foldl (fun index value => index * base + value) 0

def FiniteModel.element (model : FiniteModel) (value : Nat) : model.Element :=
  ⟨value % (model.size + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

def FiniteModel.function (model : FiniteModel) (name : String) (arguments : List model.Element) : model.Element :=
  match model.functions[(name, arguments.length)]? with
  | some table => model.element (table.read (cellIndex (model.size + 1) (arguments.map Fin.val)))
  | none => model.element 0

def FiniteModel.predicate (model : FiniteModel) (name : String) (arguments : List model.Element) : Bool :=
  match model.predicates[(name, arguments.length)]? with
  | some table => table.read (cellIndex (model.size + 1) (arguments.map Fin.val)) != 0
  | none => false

/-- The interpretation the model stands for. -/
def FiniteModel.interpretation (model : FiniteModel) : Source.Interpretation model.Element where
  function := model.function
  predicate name arguments := model.predicate name arguments = true

instance (model : FiniteModel) : Nonempty model.Element := ⟨model.element 0⟩

/-! The evaluator. Terms use `Source.Term.eval` itself; connectives short-circuit. -/

def evalFormula (model : FiniteModel) (valuation : String → model.Element) : Formula → Bool
  | .atom name arguments => model.predicate name (arguments.map (Source.Term.eval model.interpretation valuation))
  | .equal left right => decide (left.eval model.interpretation valuation = right.eval model.interpretation valuation)
  | .truth => true
  | .falsity => false
  | .neg body => !evalFormula model valuation body
  | .pair .conj left right => evalFormula model valuation left && evalFormula model valuation right
  | .pair .disj left right => evalFormula model valuation left || evalFormula model valuation right
  | .pair .implies left right => !evalFormula model valuation left || evalFormula model valuation right
  | .pair .reverse left right => !evalFormula model valuation right || evalFormula model valuation left
  | .pair .iff left right => evalFormula model valuation left == evalFormula model valuation right
  | .pair .xor left right => evalFormula model valuation left != evalFormula model valuation right
  | .pair .nand left right => !(evalFormula model valuation left && evalFormula model valuation right)
  | .pair .nor left right => !(evalFormula model valuation left || evalFormula model valuation right)
  | .all name body => (List.finRange (model.size + 1)).all fun value =>
      evalFormula model (NamedQuantified.update valuation name value) body
  | .ex name body => (List.finRange (model.size + 1)).any fun value =>
      evalFormula model (NamedQuantified.update valuation name value) body

theorem evalFormula_iff (model : FiniteModel) (formula : Formula) (valuation : String → model.Element) :
    evalFormula model valuation formula = true ↔ formula.Holds model.interpretation valuation := by
  induction formula generalizing valuation with
  | atom name arguments => simp [evalFormula, Formula.Holds, FiniteModel.interpretation]
  | equal left right => simp [evalFormula, Formula.Holds]
  | truth => simp [evalFormula, Formula.Holds]
  | falsity => simp [evalFormula, Formula.Holds]
  | neg body ih =>
    simp only [evalFormula, Formula.Holds, ← ih valuation]
    cases evalFormula model valuation body <;> simp
  | pair operator left right ihl ihr =>
    simp only [Formula.Holds, ← ihl valuation, ← ihr valuation]
    cases operator <;> simp only [evalFormula, Binary.meaning] <;>
      cases evalFormula model valuation left <;> cases evalFormula model valuation right <;> simp
  | all name body ih => simp [evalFormula, Formula.Holds, ih, List.mem_finRange]
  | ex name body ih => simp [evalFormula, Formula.Holds, ih, List.mem_finRange]

/-! A formula depends only on the values of the variables it may use. -/

theorem term_eval_agree {D : Type} (model : Source.Interpretation D) {bound : List String}
    {left right : String → D} (same : ∀ name ∈ bound, left name = right name) (term : Source.Term)
    (within : NamedQuantified.TermWithin bound term) : term.eval model left = term.eval model right := by
  cases term with
  | var name =>
    simp only [NamedQuantified.TermWithin] at within
    simp only [Source.Term.eval]
    exact same name within
  | app symbol arguments =>
    simp only [NamedQuantified.TermWithin] at within
    simp only [Source.Term.eval]
    congr 1
    apply List.map_congr_left
    intro child member
    exact term_eval_agree model same child (within child member)
termination_by sizeOf term

theorem update_agree {D : Type} {bound : List String} {left right : String → D}
    (same : ∀ name ∈ bound, left name = right name) (binder : String) (value : D) :
    ∀ name ∈ binder :: bound,
      NamedQuantified.update left binder value name = NamedQuantified.update right binder value name := by
  intro name member
  by_cases equal : name = binder
  · simp [NamedQuantified.update, equal]
  · simp only [NamedQuantified.update, equal, ↓reduceIte]
    exact same name ((List.mem_cons.mp member).resolve_left equal)

theorem holds_agree {D : Type} (model : Source.Interpretation D) (formula : Formula) :
    ∀ {bound : List String} {left right : String → D}, (∀ name ∈ bound, left name = right name) →
      formula.Within bound → (formula.Holds model left ↔ formula.Holds model right) := by
  induction formula with
  | atom name arguments =>
    intro bound left right same within
    simp only [Formula.Within] at within
    have values : arguments.map (Source.Term.eval model left) = arguments.map (Source.Term.eval model right) :=
      List.map_congr_left (fun term member => term_eval_agree model same term (within term member))
    simp only [Formula.Holds, values]
  | equal first second =>
    intro bound left right same within
    simp only [Formula.Within] at within
    simp only [Formula.Holds, term_eval_agree model same first within.1, term_eval_agree model same second within.2]
  | truth => intro _ _ _ _ _; exact Iff.rfl
  | falsity => intro _ _ _ _ _; exact Iff.rfl
  | neg body ih =>
    intro bound left right same within
    simp only [Formula.Within] at within
    exact not_congr (ih same within)
  | pair operator first second ihFirst ihSecond =>
    intro bound left right same within
    simp only [Formula.Within] at within
    simp only [Formula.Holds]
    rw [ihFirst same within.1, ihSecond same within.2]
  | all name body ih =>
    intro bound left right same within
    simp only [Formula.Within] at within
    exact forall_congr' fun value => ih (update_agree same name value) within
  | ex name body ih =>
    intro bound left right same within
    simp only [Formula.Within] at within
    exact exists_congr fun value => ih (update_agree same name value) within

/-! A Boolean scope test, proved equal to `Formula.Within`. -/

mutual
def termWithin (bound : List String) : Source.Term → Bool
  | .var name => bound.contains name
  | .app _ arguments => termsWithin bound arguments
def termsWithin (bound : List String) : List Source.Term → Bool
  | [] => true
  | term :: rest => termWithin bound term && termsWithin bound rest
end

def formulaWithin (bound : List String) : Formula → Bool
  | .atom _ arguments => termsWithin bound arguments
  | .equal left right => termWithin bound left && termWithin bound right
  | .truth | .falsity => true
  | .neg body => formulaWithin bound body
  | .pair _ left right => formulaWithin bound left && formulaWithin bound right
  | .all name body | .ex name body => formulaWithin (name :: bound) body

mutual
theorem termWithin_iff (bound : List String) (term : Source.Term) :
    termWithin bound term = true ↔ NamedQuantified.TermWithin bound term := by
  cases term with
  | var name => simp [termWithin, NamedQuantified.TermWithin]
  | app symbol arguments =>
    simp only [termWithin, NamedQuantified.TermWithin]
    exact termsWithin_iff bound arguments
theorem termsWithin_iff (bound : List String) (terms : List Source.Term) :
    termsWithin bound terms = true ↔ ∀ term ∈ terms, NamedQuantified.TermWithin bound term := by
  cases terms with
  | nil => simp [termsWithin]
  | cons term rest =>
    simp only [termsWithin, Bool.and_eq_true, termWithin_iff, termsWithin_iff, List.forall_mem_cons]
end

theorem formulaWithin_iff (bound : List String) (formula : Formula) :
    formulaWithin bound formula = true ↔ formula.Within bound := by
  induction formula generalizing bound with
  | atom name arguments => simp only [formulaWithin, Formula.Within, termsWithin_iff]
  | equal left right => simp only [formulaWithin, Formula.Within, Bool.and_eq_true, termWithin_iff]
  | truth => simp [formulaWithin, Formula.Within]
  | falsity => simp [formulaWithin, Formula.Within]
  | neg body ih => simp only [formulaWithin, Formula.Within, ih]
  | pair operator left right ihl ihr => simp only [formulaWithin, Formula.Within, Bool.and_eq_true, ihl, ihr]
  | all name body ih => simp only [formulaWithin, Formula.Within, ih]
  | ex name body ih => simp only [formulaWithin, Formula.Within, ih]

/-! Free variable names. Only the scope test above is trusted to confirm them. -/

mutual
def termNames : Source.Term → List String
  | .var name => [name]
  | .app _ arguments => termsNames arguments
def termsNames : List Source.Term → List String
  | [] => []
  | term :: rest => termNames term ++ termsNames rest
end

def freeNames (bound : List String) : Formula → List String
  | .atom _ arguments => (termsNames arguments).filter fun name => !bound.contains name
  | .equal left right => (termNames left ++ termNames right).filter fun name => !bound.contains name
  | .truth | .falsity => []
  | .neg body => freeNames bound body
  | .pair _ left right => freeNames bound left ++ freeNames bound right
  | .all name body | .ex name body => freeNames (name :: bound) body

def freeVariables (formula : Formula) : List String :=
  (freeNames [] formula).eraseDups

/-! Every assignment of a list of variables. -/

def evalAll (model : FiniteModel) (test : (String → model.Element) → Bool) :
    List String → (String → model.Element) → Bool
  | [], valuation => test valuation
  | name :: rest, valuation => (List.finRange (model.size + 1)).all fun value =>
      evalAll model test rest (NamedQuantified.update valuation name value)

theorem evalAll_complete (model : FiniteModel) {test : (String → model.Element) → Bool}
    (passes : ∀ valuation, test valuation = true) :
    ∀ (names : List String) (base : String → model.Element), evalAll model test names base = true := by
  intro names
  induction names with
  | nil => intro base; exact passes base
  | cons name rest ih =>
    intro base
    simp only [evalAll, List.all_eq_true]
    intro value _
    exact ih _

/-- Acceptance covers every valuation that agrees with the base outside the listed names. -/
theorem evalAll_sound (model : FiniteModel) {test : (String → model.Element) → Bool} :
    ∀ (names : List String) (base : String → model.Element), evalAll model test names base = true →
      ∀ valuation, (∀ name, name ∉ names → valuation name = base name) → test valuation = true := by
  intro names
  induction names with
  | nil =>
    intro base accepted valuation outside
    have same : valuation = base := funext fun name => outside name (by simp)
    subst same
    exact accepted
  | cons first rest ih =>
    intro base accepted valuation outside
    simp only [evalAll, List.all_eq_true] at accepted
    apply ih (NamedQuantified.update base first (valuation first))
      (accepted (valuation first) (List.mem_finRange _)) valuation
    intro name absent
    by_cases equal : name = first
    · subst equal
      simp [NamedQuantified.update]
    · simp only [NamedQuantified.update, equal, ↓reduceIte]
      exact outside name (by simp [equal, absent])

/-! Deciding a sentence: the formula under every valuation. -/

/-- `none` when the computed variable list does not cover the formula; otherwise the truth value of
    `∀ valuation, formula.Holds model.interpretation valuation`. -/
def sentenceValue (model : FiniteModel) (formula : Formula) : Option Bool :=
  if formulaWithin (freeVariables formula) formula then
    some (evalAll model (fun valuation => evalFormula model valuation formula) (freeVariables formula)
      (fun _ => model.element 0))
  else none

theorem sentenceValue_iff {model : FiniteModel} {formula : Formula} {value : Bool}
    (computed : sentenceValue model formula = some value) :
    value = true ↔ ∀ valuation, formula.Holds model.interpretation valuation := by
  unfold sentenceValue at computed
  split at computed
  · rename_i covered
    have within := (formulaWithin_iff _ formula).mp covered
    cases computed
    constructor
    · intro accepted valuation
      classical
      let base : String → model.Element := fun _ => model.element 0
      let joined : String → model.Element := fun name =>
        if name ∈ freeVariables formula then valuation name else base name
      have passes := evalAll_sound model (freeVariables formula) base accepted joined (by
        intro name absent
        simp only [joined, absent, ↓reduceIte])
      have holds := (evalFormula_iff model formula joined).mp passes
      refine (holds_agree model.interpretation formula ?_ within).mp holds
      intro name member
      simp only [joined, member, ↓reduceIte]
    · intro holds
      exact evalAll_complete model (fun valuation => (evalFormula_iff model formula valuation).mpr (holds valuation)) _ _
  · cases computed

/-! Distinct objects. -/

def separated (model : FiniteModel) (names : List String) : Bool :=
  names.all fun left => names.all fun right =>
    left == right || model.function left [] != model.function right []

theorem separated_iff (model : FiniteModel) (names : List String) :
    separated model names = true ↔ ∀ left ∈ names, ∀ right ∈ names, left ≠ right →
      model.interpretation.function left [] ≠ model.interpretation.function right [] := by
  simp only [separated, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · intro accepted left leftMember right rightMember different
    rcases accepted left leftMember right rightMember with same | apart
    · exact absurd same different
    · exact apart
  · intro separate left leftMember right rightMember
    by_cases same : left = right
    · exact Or.inl same
    · exact Or.inr (separate left leftMember right rightMember same)

/-! Checking a list of statements. -/

inductive Rejection where
  /-- The computed variable list did not cover statement `index`; a checker fault, never a result. -/
  | scope : Nat → Rejection
  /-- Statement `index` is false in the model. -/
  | statement : Nat → Rejection
  deriving Repr, DecidableEq

def checkFrom (model : FiniteModel) : Nat → List Formula → Except Rejection Unit
  | _, [] => .ok ()
  | index, formula :: rest =>
    match sentenceValue model formula with
    | some true => checkFrom model (index + 1) rest
    | some false => .error (.statement index)
    | none => .error (.scope index)

theorem checkFrom_sound (model : FiniteModel) :
    ∀ (index : Nat) (formulas : List Formula), checkFrom model index formulas = .ok () →
      ∀ formula ∈ formulas, ∀ valuation, formula.Holds model.interpretation valuation := by
  intro index formulas
  induction formulas generalizing index with
  | nil => intro _ formula member; cases member
  | cons first rest ih =>
    intro accepted formula member
    unfold checkFrom at accepted
    split at accepted
    · rename_i computed
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact (sentenceValue_iff computed).mp rfl
      · exact ih (index + 1) accepted formula later
    · cases accepted
    · cases accepted

/-! The static work estimate of the first version: an upper bound on evaluated nodes. The entries no longer use it; the step budget of `ModelSteps` bounds the work, and the control `static_estimate_refuses` compares the two. -/

mutual
def termSize : Source.Term → Nat
  | .var _ => 1
  | .app _ arguments => 1 + termsSize arguments
def termsSize : List Source.Term → Nat
  | [] => 0
  | term :: rest => termSize term + termsSize rest
end

/-- Each node counts `weight`, the number of valuations it is evaluated under; a binder multiplies it by the
    domain size. -/
def formulaCost (base : Nat) : Nat → Formula → Nat
  | weight, .atom _ arguments => weight * (1 + termsSize arguments)
  | weight, .equal left right => weight * (1 + termSize left + termSize right)
  | weight, .truth | weight, .falsity => weight
  | weight, .neg body => weight + formulaCost base weight body
  | weight, .pair _ left right => weight + formulaCost base weight left + formulaCost base weight right
  | weight, .all _ body | weight, .ex _ body => weight + formulaCost base (weight * base) body

def sentenceCost (model : FiniteModel) (formula : Formula) : Nat :=
  formulaCost (model.size + 1) ((model.size + 1) ^ (freeVariables formula).length) formula

def workOf (model : FiniteModel) (formulas : List Formula) : Nat :=
  formulas.foldl (fun total formula => total + sentenceCost model formula) 0

/-! Small `Except` facts used by the entries. -/

theorem bind_ok {ε α β : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (success : (action >>= next) = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error reason => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem mapError_ok {ε ε' α : Type} {action : Except ε α} {wrap : ε → ε'} {value : α}
    (success : action.mapError wrap = .ok value) : action = .ok value := by
  cases action with
  | error reason => cases success
  | ok inner => cases success; rfl

end Fang.TptpCandidate.FullFof.Model
