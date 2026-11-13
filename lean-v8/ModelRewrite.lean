/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   A rewriting pass that moves quantifiers inward before evaluation, proved to keep the meaning of every formula over
   every nonempty domain (`rewrite_holds`). Rules: a quantifier is swapped with one of the same kind below it,
   distributed over the connective it commutes with (`∀` over `&`, `∃` over `|`), moved past a side of `|`, `&`,
   `=>`, `<=` that does not use its variable (turning into the dual quantifier on an antecedent), moved through
   negation as the dual quantifier, and dropped when its variable does not occur free; a conjunctive antecedent is
   curried, `(A & B) => C` to `A => (B => C)`. Evaluating the rewritten formula visits fewer valuations when a
   quantifier ends up under a connective that short-circuits. This module imports no extracted code. -/
import ModelSemantics

namespace Fang.TptpCandidate.FullFof.Model

open NamedQuantified (update)

/-! Free occurrence of a variable. -/

mutual
def termHas (name : String) : Source.Term → Bool
  | .var other => other == name
  | .app _ arguments => termsHave name arguments
def termsHave (name : String) : List Source.Term → Bool
  | [] => false
  | term :: rest => termHas name term || termsHave name rest
end

def freeIn (name : String) : Formula → Bool
  | .atom _ arguments => termsHave name arguments
  | .equal left right => termHas name left || termHas name right
  | .truth | .falsity => false
  | .neg body => freeIn name body
  | .pair _ left right => freeIn name left || freeIn name right
  | .all binder body | .ex binder body => binder != name && freeIn name body

theorem update_same {D : Type} (valuation : String → D) (name : String) (first second : D) :
    update (update valuation name first) name second = update valuation name second := by
  funext other
  by_cases equal : other = name <;> simp [update, equal]

theorem update_comm {D : Type} (valuation : String → D) {first second : String} (different : first ≠ second)
    (one other : D) :
    update (update valuation first one) second other = update (update valuation second other) first one := by
  funext name
  by_cases atFirst : name = first
  · subst atFirst
    simp [update, different]
  · by_cases atSecond : name = second
    · subst atSecond
      simp [update, atFirst]
    · simp [update, atFirst, atSecond]

mutual
theorem term_update_eval {D : Type} (model : Source.Interpretation D) (valuation : String → D) (name : String)
    (value : D) (term : Source.Term) (absent : termHas name term = false) :
    term.eval model (update valuation name value) = term.eval model valuation := by
  cases term with
  | var other =>
    simp only [termHas, beq_eq_false_iff_ne, ne_eq] at absent
    simp [Source.Term.eval, update, absent]
  | app symbol arguments =>
    simp only [termHas] at absent
    simp only [Source.Term.eval]
    rw [terms_update_eval model valuation name value arguments absent]
theorem terms_update_eval {D : Type} (model : Source.Interpretation D) (valuation : String → D) (name : String)
    (value : D) (terms : List Source.Term) (absent : termsHave name terms = false) :
    terms.map (Source.Term.eval model (update valuation name value)) = terms.map (Source.Term.eval model valuation) := by
  cases terms with
  | nil => rfl
  | cons term rest =>
    simp only [termsHave, Bool.or_eq_false_iff] at absent
    simp only [List.map_cons, term_update_eval model valuation name value term absent.1,
      terms_update_eval model valuation name value rest absent.2]
end

/-- A variable that does not occur free does not matter. -/
theorem holds_update_absent {D : Type} (model : Source.Interpretation D) (name : String) (value : D)
    (formula : Formula) : ∀ (valuation : String → D), freeIn name formula = false →
      (formula.Holds model (update valuation name value) ↔ formula.Holds model valuation) := by
  induction formula with
  | atom predicate arguments =>
    intro valuation absent
    simp only [freeIn] at absent
    simp only [Formula.Holds, terms_update_eval model valuation name value arguments absent]
  | equal left right =>
    intro valuation absent
    simp only [freeIn, Bool.or_eq_false_iff] at absent
    simp only [Formula.Holds, term_update_eval model valuation name value left absent.1,
      term_update_eval model valuation name value right absent.2]
  | truth => intro _ _; exact Iff.rfl
  | falsity => intro _ _; exact Iff.rfl
  | neg body ih =>
    intro valuation absent
    exact not_congr (ih valuation absent)
  | pair operator left right ihLeft ihRight =>
    intro valuation absent
    simp only [freeIn, Bool.or_eq_false_iff] at absent
    simp only [Formula.Holds]
    rw [ihLeft valuation absent.1, ihRight valuation absent.2]
  | all binder body ih =>
    intro valuation absent
    simp only [Formula.Holds]
    by_cases same : binder = name
    · subst same
      simp only [update_same]
    · have inner : freeIn name body = false := by
        simp only [freeIn, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at absent
        exact absent.resolve_left same
      apply forall_congr'
      intro other
      rw [update_comm valuation (Ne.symm same) value other]
      exact ih _ inner
  | ex binder body ih =>
    intro valuation absent
    simp only [Formula.Holds]
    by_cases same : binder = name
    · subst same
      simp only [update_same]
    · have inner : freeIn name body = false := by
        simp only [freeIn, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at absent
        exact absent.resolve_left same
      apply exists_congr
      intro other
      rw [update_comm valuation (Ne.symm same) value other]
      exact ih _ inner

/-! Moving one quantifier inward. -/

mutual
/-- `∀ name, formula`, with the quantifier moved as far inward as the rules allow. -/
def pushAll (name : String) : Formula → Formula
  | .pair .conj left right => .pair .conj (pushAll name left) (pushAll name right)
  | .pair .disj left right =>
    if freeIn name right then
      if freeIn name left then .all name (.pair .disj left right) else .pair .disj left (pushAll name right)
    else .pair .disj (pushAll name left) right
  | .pair .implies left right =>
    if freeIn name left then
      if freeIn name right then .all name (.pair .implies left right) else .pair .implies (pushEx name left) right
    else .pair .implies left (pushAll name right)
  | .pair .reverse left right =>
    if freeIn name right then
      if freeIn name left then .all name (.pair .reverse left right) else .pair .reverse left (pushEx name right)
    else .pair .reverse (pushAll name left) right
  | .pair .nor left right => .pair .nor (pushEx name left) (pushEx name right)
  | .neg body => .neg (pushEx name body)
  | .all binder body =>
    if binder = name then .all binder body else .all binder (pushAll name body)
  | formula => if freeIn name formula then .all name formula else formula
/-- `∃ name, formula`, with the quantifier moved as far inward as the rules allow. -/
def pushEx (name : String) : Formula → Formula
  | .pair .disj left right => .pair .disj (pushEx name left) (pushEx name right)
  | .pair .conj left right =>
    if freeIn name right then
      if freeIn name left then .ex name (.pair .conj left right) else .pair .conj left (pushEx name right)
    else .pair .conj (pushEx name left) right
  | .pair .implies left right => .pair .implies (pushAll name left) (pushEx name right)
  | .pair .reverse left right => .pair .reverse (pushEx name left) (pushAll name right)
  | .pair .nand left right => .pair .nand (pushAll name left) (pushAll name right)
  | .neg body => .neg (pushAll name body)
  | .ex binder body =>
    if binder = name then .ex binder body else .ex binder (pushEx name body)
  | formula => if freeIn name formula then .ex name formula else formula
end

/-- `A => C` with every conjunct of `A` curried: `(A1 & A2) => C` becomes `A1 => (A2 => C)`. -/
def curryImplies : Formula → Formula → Formula
  | .pair .conj first second, conclusion => curryImplies first (curryImplies second conclusion)
  | antecedent, conclusion => .pair .implies antecedent conclusion

/-- The pass, from the leaves up. -/
def rewrite : Formula → Formula
  | .all name body => pushAll name (rewrite body)
  | .ex name body => pushEx name (rewrite body)
  | .neg body => .neg (rewrite body)
  | .pair .implies left right => curryImplies (rewrite left) (rewrite right)
  | .pair operator left right => .pair operator (rewrite left) (rewrite right)
  | formula => formula

/-! Meaning. -/

section Meaning

variable {D : Type} [Nonempty D] (model : Source.Interpretation D)

theorem fallbackAll_holds (name : String) (formula : Formula) (valuation : String → D) :
    (if freeIn name formula then Formula.all name formula else formula).Holds model valuation ↔
      ∀ value, formula.Holds model (update valuation name value) := by
  by_cases occurs : freeIn name formula
  · simp only [occurs, ↓reduceIte, Formula.Holds]
  · simp only [occurs, Bool.false_eq_true, ↓reduceIte]
    have absent : freeIn name formula = false := by simpa using occurs
    constructor
    · intro holds value
      exact (holds_update_absent model name value formula valuation absent).mpr holds
    · intro holds
      obtain ⟨value⟩ := ‹Nonempty D›
      exact (holds_update_absent model name value formula valuation absent).mp (holds value)

theorem fallbackEx_holds (name : String) (formula : Formula) (valuation : String → D) :
    (if freeIn name formula then Formula.ex name formula else formula).Holds model valuation ↔
      ∃ value, formula.Holds model (update valuation name value) := by
  by_cases occurs : freeIn name formula
  · simp only [occurs, ↓reduceIte, Formula.Holds]
  · simp only [occurs, Bool.false_eq_true, ↓reduceIte]
    have absent : freeIn name formula = false := by simpa using occurs
    constructor
    · intro holds
      obtain ⟨value⟩ := ‹Nonempty D›
      exact ⟨value, (holds_update_absent model name value formula valuation absent).mpr holds⟩
    · rintro ⟨value, holds⟩
      exact (holds_update_absent model name value formula valuation absent).mp holds

theorem absent_of_not {name : String} {formula : Formula} (occurs : ¬ freeIn name formula = true) :
    freeIn name formula = false := by
  simpa using occurs

/-- Both directions of moving a quantifier inward keep the meaning. -/
theorem push_holds (name : String) (formula : Formula) :
    (∀ valuation, (pushAll name formula).Holds model valuation ↔
        ∀ value, formula.Holds model (update valuation name value)) ∧
      (∀ valuation, (pushEx name formula).Holds model valuation ↔
        ∃ value, formula.Holds model (update valuation name value)) := by
  induction formula with
  | atom predicate arguments =>
    exact ⟨fun valuation => by simp only [pushAll]; exact fallbackAll_holds model name _ valuation,
      fun valuation => by simp only [pushEx]; exact fallbackEx_holds model name _ valuation⟩
  | equal left right =>
    exact ⟨fun valuation => by simp only [pushAll]; exact fallbackAll_holds model name _ valuation,
      fun valuation => by simp only [pushEx]; exact fallbackEx_holds model name _ valuation⟩
  | truth =>
    exact ⟨fun valuation => by simp only [pushAll]; exact fallbackAll_holds model name _ valuation,
      fun valuation => by simp only [pushEx]; exact fallbackEx_holds model name _ valuation⟩
  | falsity =>
    exact ⟨fun valuation => by simp only [pushAll]; exact fallbackAll_holds model name _ valuation,
      fun valuation => by simp only [pushEx]; exact fallbackEx_holds model name _ valuation⟩
  | neg body ih =>
    refine ⟨fun valuation => ?_, fun valuation => ?_⟩
    · simp only [pushAll, Formula.Holds]
      rw [ih.2 valuation]
      exact not_exists
    · simp only [pushEx, Formula.Holds]
      rw [ih.1 valuation]
      exact Classical.not_forall
  | all binder body ih =>
    refine ⟨fun valuation => ?_, fun valuation => ?_⟩
    · simp only [pushAll]
      by_cases same : binder = name
      · subst same
        simp only [↓reduceIte, Formula.Holds, update_same]
        constructor
        · intro holds _
          exact holds
        · intro holds
          obtain ⟨value⟩ := ‹Nonempty D›
          exact holds value
      · simp only [same, ↓reduceIte, Formula.Holds]
        rw [forall_comm]
        apply forall_congr'
        intro other
        rw [ih.1 (update valuation binder other)]
        apply forall_congr'
        intro value
        rw [update_comm valuation (Ne.symm same) value other]
    · simp only [pushEx]
      exact fallbackEx_holds model name _ valuation
  | ex binder body ih =>
    refine ⟨fun valuation => ?_, fun valuation => ?_⟩
    · simp only [pushAll]
      exact fallbackAll_holds model name _ valuation
    · simp only [pushEx]
      by_cases same : binder = name
      · subst same
        simp only [↓reduceIte, Formula.Holds, update_same]
        constructor
        · intro holds
          obtain ⟨value⟩ := ‹Nonempty D›
          exact ⟨value, holds⟩
        · rintro ⟨_, holds⟩
          exact holds
      · simp only [same, ↓reduceIte, Formula.Holds]
        rw [exists_comm]
        apply exists_congr
        intro other
        rw [ih.2 (update valuation binder other)]
        apply exists_congr
        intro value
        rw [update_comm valuation (Ne.symm same) value other]
  | pair operator left right ihLeft ihRight =>
    have keepLeft := fun value valuation (absent : freeIn name left = false) =>
      holds_update_absent model name value left valuation absent
    have keepRight := fun value valuation (absent : freeIn name right = false) =>
      holds_update_absent model name value right valuation absent
    cases operator with
    | conj =>
      refine ⟨fun valuation => ?_, fun valuation => ?_⟩
      · simp only [pushAll, Formula.Holds, Binary.meaning]
        rw [ihLeft.1 valuation, ihRight.1 valuation]
        exact forall_and.symm
      · simp only [pushEx]
        by_cases inRight : freeIn name right = true
        · by_cases inLeft : freeIn name left = true
          · simp only [inRight, inLeft, ↓reduceIte, Formula.Holds]
          · simp only [inRight, inLeft, ↓reduceIte, Bool.false_eq_true, Formula.Holds, Binary.meaning]
            rw [ihRight.2 valuation]
            constructor
            · rintro ⟨holds, value, other⟩
              exact ⟨value, (keepLeft value valuation (absent_of_not inLeft)).mpr holds, other⟩
            · rintro ⟨value, holds, other⟩
              exact ⟨(keepLeft value valuation (absent_of_not inLeft)).mp holds, value, other⟩
        · simp only [inRight, ↓reduceIte, Bool.false_eq_true, Formula.Holds, Binary.meaning]
          rw [ihLeft.2 valuation]
          constructor
          · rintro ⟨⟨value, holds⟩, other⟩
            exact ⟨value, holds, (keepRight value valuation (absent_of_not inRight)).mpr other⟩
          · rintro ⟨value, holds, other⟩
            exact ⟨⟨value, holds⟩, (keepRight value valuation (absent_of_not inRight)).mp other⟩
    | disj =>
      refine ⟨fun valuation => ?_, fun valuation => ?_⟩
      · simp only [pushAll]
        by_cases inRight : freeIn name right = true
        · by_cases inLeft : freeIn name left = true
          · simp only [inRight, inLeft, ↓reduceIte, Formula.Holds]
          · simp only [inRight, inLeft, ↓reduceIte, Bool.false_eq_true, Formula.Holds, Binary.meaning]
            rw [ihRight.1 valuation]
            constructor
            · rintro (holds | holds) value
              · exact Or.inl ((keepLeft value valuation (absent_of_not inLeft)).mpr holds)
              · exact Or.inr (holds value)
            · intro holds
              by_cases first : left.Holds model valuation
              · exact Or.inl first
              · refine Or.inr fun value => ?_
                rcases holds value with other | other
                · exact absurd ((keepLeft value valuation (absent_of_not inLeft)).mp other) first
                · exact other
        · simp only [inRight, ↓reduceIte, Bool.false_eq_true, Formula.Holds, Binary.meaning]
          rw [ihLeft.1 valuation]
          constructor
          · rintro (holds | holds) value
            · exact Or.inl (holds value)
            · exact Or.inr ((keepRight value valuation (absent_of_not inRight)).mpr holds)
          · intro holds
            by_cases second : right.Holds model valuation
            · exact Or.inr second
            · refine Or.inl fun value => ?_
              rcases holds value with other | other
              · exact other
              · exact absurd ((keepRight value valuation (absent_of_not inRight)).mp other) second
      · simp only [pushEx, Formula.Holds, Binary.meaning]
        rw [ihLeft.2 valuation, ihRight.2 valuation]
        exact exists_or.symm
    | implies =>
      refine ⟨fun valuation => ?_, fun valuation => ?_⟩
      · simp only [pushAll]
        by_cases inLeft : freeIn name left = true
        · by_cases inRight : freeIn name right = true
          · simp only [inRight, inLeft, ↓reduceIte, Formula.Holds]
          · simp only [inRight, inLeft, ↓reduceIte, Bool.false_eq_true, Formula.Holds, Binary.meaning]
            rw [ihLeft.2 valuation]
            constructor
            · intro holds value first
              exact (keepRight value valuation (absent_of_not inRight)).mpr (holds ⟨value, first⟩)
            · rintro holds ⟨value, first⟩
              exact (keepRight value valuation (absent_of_not inRight)).mp (holds value first)
        · simp only [inLeft, ↓reduceIte, Bool.false_eq_true, Formula.Holds, Binary.meaning]
          rw [ihRight.1 valuation]
          constructor
          · intro holds value first
            exact holds ((keepLeft value valuation (absent_of_not inLeft)).mp first) value
          · intro holds first value
            exact holds value ((keepLeft value valuation (absent_of_not inLeft)).mpr first)
      · simp only [pushEx, Formula.Holds, Binary.meaning]
        rw [ihLeft.1 valuation, ihRight.2 valuation]
        constructor
        · intro holds
          by_cases every : ∀ value, left.Holds model (update valuation name value)
          · obtain ⟨value, other⟩ := holds every
            exact ⟨value, fun _ => other⟩
          · obtain ⟨value, fails⟩ := Classical.not_forall.mp every
            exact ⟨value, fun first => absurd first fails⟩
        · rintro ⟨value, holds⟩ every
          exact ⟨value, holds (every value)⟩
    | reverse =>
      refine ⟨fun valuation => ?_, fun valuation => ?_⟩
      · simp only [pushAll]
        by_cases inRight : freeIn name right = true
        · by_cases inLeft : freeIn name left = true
          · simp only [inRight, inLeft, ↓reduceIte, Formula.Holds]
          · simp only [inRight, inLeft, ↓reduceIte, Bool.false_eq_true, Formula.Holds, Binary.meaning]
            rw [ihRight.2 valuation]
            constructor
            · intro holds value second
              exact (keepLeft value valuation (absent_of_not inLeft)).mpr (holds ⟨value, second⟩)
            · rintro holds ⟨value, second⟩
              exact (keepLeft value valuation (absent_of_not inLeft)).mp (holds value second)
        · simp only [inRight, ↓reduceIte, Bool.false_eq_true, Formula.Holds, Binary.meaning]
          rw [ihLeft.1 valuation]
          constructor
          · intro holds value second
            exact holds ((keepRight value valuation (absent_of_not inRight)).mp second) value
          · intro holds second value
            exact holds value ((keepRight value valuation (absent_of_not inRight)).mpr second)
      · simp only [pushEx, Formula.Holds, Binary.meaning]
        rw [ihLeft.2 valuation, ihRight.1 valuation]
        constructor
        · intro holds
          by_cases every : ∀ value, right.Holds model (update valuation name value)
          · obtain ⟨value, other⟩ := holds every
            exact ⟨value, fun _ => other⟩
          · obtain ⟨value, fails⟩ := Classical.not_forall.mp every
            exact ⟨value, fun second => absurd second fails⟩
        · rintro ⟨value, holds⟩ every
          exact ⟨value, holds (every value)⟩
    | nand =>
      refine ⟨fun valuation => ?_, fun valuation => ?_⟩
      · simp only [pushAll]
        exact fallbackAll_holds model name _ valuation
      · simp only [pushEx, Formula.Holds, Binary.meaning]
        rw [ihLeft.1 valuation, ihRight.1 valuation]
        constructor
        · intro holds
          apply Classical.byContradiction
          intro none
          exact holds ⟨fun value => Classical.byContradiction fun fails => none ⟨value, fun both => fails both.1⟩,
            fun value => Classical.byContradiction fun fails => none ⟨value, fun both => fails both.2⟩⟩
        · rintro ⟨value, holds⟩ ⟨first, second⟩
          exact holds ⟨first value, second value⟩
    | nor =>
      refine ⟨fun valuation => ?_, fun valuation => ?_⟩
      · simp only [pushAll, Formula.Holds, Binary.meaning]
        rw [ihLeft.2 valuation, ihRight.2 valuation]
        constructor
        · intro holds value either
          rcases either with first | second
          · exact holds (Or.inl ⟨value, first⟩)
          · exact holds (Or.inr ⟨value, second⟩)
        · rintro holds (⟨value, first⟩ | ⟨value, second⟩)
          · exact holds value (Or.inl first)
          · exact holds value (Or.inr second)
      · simp only [pushEx]
        exact fallbackEx_holds model name _ valuation
    | iff =>
      exact ⟨fun valuation => by simp only [pushAll]; exact fallbackAll_holds model name _ valuation,
        fun valuation => by simp only [pushEx]; exact fallbackEx_holds model name _ valuation⟩
    | xor =>
      exact ⟨fun valuation => by simp only [pushAll]; exact fallbackAll_holds model name _ valuation,
        fun valuation => by simp only [pushEx]; exact fallbackEx_holds model name _ valuation⟩

omit [Nonempty D] in
theorem curryImplies_holds (antecedent : Formula) :
    ∀ (conclusion : Formula) (valuation : String → D),
      (curryImplies antecedent conclusion).Holds model valuation ↔
        (antecedent.Holds model valuation → conclusion.Holds model valuation) := by
  induction antecedent with
  | pair operator first second ihFirst ihSecond =>
    intro conclusion valuation
    cases operator with
    | conj =>
      simp only [curryImplies]
      rw [ihFirst, ihSecond]
      simp only [Formula.Holds, Binary.meaning]
      exact ⟨fun holds both => holds both.1 both.2, fun holds first second => holds ⟨first, second⟩⟩
    | _ => simp only [curryImplies, Formula.Holds, Binary.meaning]
  | _ => intro conclusion valuation; simp only [curryImplies, Formula.Holds, Binary.meaning]

/-- The pass keeps the meaning of every formula under every valuation. -/
theorem rewrite_holds (formula : Formula) :
    ∀ (valuation : String → D), (rewrite formula).Holds model valuation ↔ formula.Holds model valuation := by
  induction formula with
  | all name body ih =>
    intro valuation
    simp only [rewrite, Formula.Holds]
    rw [(push_holds model name (rewrite body)).1 valuation]
    exact forall_congr' fun value => ih _
  | ex name body ih =>
    intro valuation
    simp only [rewrite, Formula.Holds]
    rw [(push_holds model name (rewrite body)).2 valuation]
    exact exists_congr fun value => ih _
  | neg body ih =>
    intro valuation
    simp only [rewrite, Formula.Holds]
    rw [ih valuation]
  | pair operator left right ihLeft ihRight =>
    intro valuation
    cases operator with
    | implies =>
      simp only [rewrite]
      rw [curryImplies_holds model, ihLeft valuation, ihRight valuation]
      simp only [Formula.Holds, Binary.meaning]
    | _ =>
      simp only [rewrite, Formula.Holds]
      rw [ihLeft valuation, ihRight valuation]
  | _ => intro valuation; simp only [rewrite]

end Meaning

end Fang.TptpCandidate.FullFof.Model
