/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import FofProblemSound

namespace Fang.TptpCandidate.FullFof
open NamedQuantified

theorem term_arguments_within (fuel : Nat) :
    (∀ depth bound endOffset input value rest,
      term fuel depth (some bound) endOffset input = .ok (value, rest) → TermWithin bound value) ∧
    (∀ depth bound endOffset input values rest,
      arguments fuel depth (some bound) endOffset input = .ok (values, rest) →
        ∀ value ∈ values, TermWithin bound value) := by
  induction fuel with
  | zero =>
    constructor
    · intro depth bound endOffset input value rest success
      simp [term, failure] at success
    · intro depth bound endOffset input values rest success
      simp [arguments, failure] at success
  | succ fuel ih =>
    constructor
    · intro depth bound endOffset input value final success
      simp only [term, failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ _ token rest _ name kind member
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        simpa [TermWithin] using member
      · rename_i _ _ token rest _ _ _ _ name kind opening _ args argsAt _ closing closeAt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        simpa only [TermWithin] using ih.2 _ _ _ _ _ _ argsAt
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        simp [TermWithin]
    · intro depth bound endOffset input values final success
      simp only [arguments, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ first firstAt comma _ tail tailAt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact ih.1 _ _ _ _ _ _ firstAt
        · exact ih.2 _ _ _ _ _ _ tailAt value member
      · rename_i _ first firstAt notComma
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        intro value member
        have equal : value = first.1 := by simpa using member
        subst value
        exact ih.1 _ _ _ _ _ _ firstAt

theorem term_within {fuel depth bound endOffset input value rest}
    (success : term fuel depth (some bound) endOffset input = .ok (value, rest)) :
    TermWithin bound value := (term_arguments_within fuel).1 _ _ _ _ _ _ success

theorem arguments_within {fuel depth bound endOffset input values rest}
    (success : arguments fuel depth (some bound) endOffset input = .ok (values, rest)) :
    ∀ value ∈ values, TermWithin bound value := (term_arguments_within fuel).2 _ _ _ _ _ _ success

theorem atom_within {fuel bound endOffset input value final}
    (success : atom fuel (some bound) endOffset input = .ok (value, final)) :
    value.Within bound := by
  cases headAt : term fuel 0 (some bound) endOffset input with
  | error reason => simp [atom, headAt, bind, Except.bind] at success
  | ok result =>
    rcases result with ⟨head, rest⟩
    have headWithin := term_within headAt
    cases rest with
    | nil =>
      cases head with
      | var name => simp [atom, headAt, failure, bind, Except.bind] at success
      | app name args =>
        simp [atom, headAt, bind, Except.bind, pure, Except.pure] at success
        rcases success with ⟨rfl, rfl⟩
        simpa only [TermWithin, Formula.Within] using headWithin
    | cons token middle =>
      simp only [atom, headAt, bind, Except.bind] at success
      split at success
      next positive kind =>
        cases rightAt : term fuel 0 (some bound) endOffset middle with
        | error reason => simp [rightAt] at success
        | ok result =>
          rcases result with ⟨right, rest⟩
          simp [rightAt, pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          cases positive <;> exact ⟨headWithin, term_within rightAt⟩
      next notEquality =>
        cases head with
        | var name => simp [failure] at success
        | app name args =>
          simp [pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          simpa only [TermWithin, Formula.Within] using headWithin

theorem term_within_congr (value : Source.Term) {left right : List String}
    (same : ∀ name, name ∈ left ↔ name ∈ right) : TermWithin left value ↔ TermWithin right value := by
  cases value with
  | var name => simpa only [TermWithin] using same name
  | app name args =>
    simp only [TermWithin]
    apply forall_congr'
    intro child
    apply forall_congr'
    intro member
    exact term_within_congr child same
termination_by sizeOf value

theorem formula_within_congr (value : Formula) {left right : List String}
    (same : ∀ name, name ∈ left ↔ name ∈ right) : value.Within left ↔ value.Within right := by
  induction value generalizing left right with
  | atom name args =>
    simp only [Formula.Within]
    apply forall_congr'
    intro child
    apply forall_congr'
    intro member
    exact term_within_congr child same
  | equal a b => exact and_congr (term_within_congr a same) (term_within_congr b same)
  | truth | falsity => rfl
  | neg body ih => exact ih same
  | pair operator a b ihA ihB => exact and_congr (ihA same) (ihB same)
  | all name body ih | ex name body ih =>
    exact ih (by intro other; simp only [List.mem_cons, same other])

theorem close_within (universal : Bool) (names bound : List String) (body : Formula) :
    (close universal names body).Within bound ↔ body.Within (names ++ bound) := by
  induction names generalizing bound with
  | nil => rfl
  | cons name names ih =>
    cases universal <;>
      change (close _ names body).Within (name :: bound) ↔ body.Within ((name :: names) ++ bound)
    all_goals
      rw [ih]
      exact formula_within_congr body (by intro other; simp [List.mem_append, or_left_comm])

theorem unit_formula_chain_within (fuel : Nat) :
    (∀ depth bound endOffset input value rest,
      unit fuel depth bound endOffset input = .ok (value, rest) → value.Within bound) ∧
    (∀ depth bound endOffset input value rest,
      formula fuel depth bound endOffset input = .ok (value, rest) → value.Within bound) ∧
    (∀ depth bound endOffset operator left input value rest, left.Within bound →
      chain fuel depth bound endOffset operator left input = .ok (value, rest) → value.Within bound) := by
  induction fuel with
  | zero =>
    constructor
    · intro depth bound endOffset input value rest success; simp [unit, failure] at success
    constructor
    · intro depth bound endOffset input value rest success; simp [formula, failure] at success
    · intro depth bound endOffset operator left input value rest _ success
      simp [chain, failure] at success
  | succ fuel ih =>
    constructor
    · intro depth bound endOffset input value final success
      unfold unit at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success); trivial
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success); trivial
      · rename_i _ _ token rest _ kind _ result call
        obtain ⟨rfl, rfl⟩ := checked_exact success
        exact (show Formula.Within bound result.1 from ih.1 _ _ _ _ _ _ call)
      · rename_i _ _ token rest _ kind _ result call _ closing closeAt
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact ih.2.1 _ _ _ _ _ _ call
      · rename_i _ _ token rest _ kind _ opening openAt _ names namesAt _
          _ closing closeAt _ colon colonAt _ body bodyAt
        obtain ⟨rfl, rfl⟩ := checked_exact success
        exact (close_within _ _ _ _).mpr (ih.1 _ _ _ _ _ _ bodyAt)
      · rename_i _ _ token rest _ kind _ opening openAt _ names namesAt _
          _ closing closeAt _ colon colonAt _ body bodyAt
        obtain ⟨rfl, rfl⟩ := checked_exact success
        exact (close_within _ _ _ _).mpr (ih.1 _ _ _ _ _ _ bodyAt)
      · rename_i _ _ token rest _ _ _ _ _ _ _ _ _ result call
        obtain ⟨rfl, rfl⟩ := checked_exact success
        exact atom_within call
    constructor
    · intro depth bound endOffset input value final success
      simp only [formula, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ result call _ empty
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact ih.1 _ _ _ _ _ _ call
      · rename_i _ result call _ next tail shape _ noOperator
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact ih.1 _ _ _ _ _ _ call
      · rename_i _ result call _ next tail shape _ operator operatorAt
        exact ih.2.2 _ _ _ _ _ _ _ _ (ih.1 _ _ _ _ _ _ call) success
    · intro depth bound endOffset operator left input value final leftWithin success
      unfold chain at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      · rename_i _ token rest operatorAt _ right rightAt _ checkedResult checkedAt more
        have combined : (Formula.pair operator left right.1).Within bound :=
          ⟨leftWithin, ih.1 _ _ _ _ _ _ rightAt⟩
        exact ih.2.2 _ _ _ _ _ _ _ _ combined success
      · rename_i _ token rest operatorAt _ right rightAt _ checkedResult checkedAt finished
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
        exact ⟨leftWithin, ih.1 _ _ _ _ _ _ rightAt⟩

theorem formula_within {fuel depth bound endOffset input value rest}
    (success : formula fuel depth bound endOffset input = .ok (value, rest)) : value.Within bound :=
  (unit_formula_chain_within fuel).2.1 _ _ _ _ _ _ success

theorem declaration_closed {seen endOffset input value final}
    (success : declaration seen endOffset input = .ok (value, final)) :
    match value.body with | .cnf _ => True | .fof body => body.Within [] := by
  cases input with
  | nil => simp [declaration, failure] at success
  | cons keyword rest =>
    simp only [declaration, failure, bind, Except.bind, pure, Except.pure] at success
    repeat' first | contradiction | split at success
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success); trivial
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success); trivial
    · rename_i _ keywordAt _ opened openAt _ nameToken afterName nameInput
        _ nameKind nameKindAt _ name nameAt fresh _ roleComma roleCommaAt
        _ role afterRole roleInput _ roleAt _ bodyComma bodyCommaAt _
        _ body bodyAt noAnnotation _ closing closingAt _ dot dotAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      exact formula_within bodyAt

theorem declarations_closed {fuel seen endOffset input values}
    (success : declarations fuel seen endOffset input = .ok values) : Grammar.Closed values := by
  induction fuel generalizing seen input values with
  | zero => simp [declarations, failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarations] at success
      subst values
      simp [Grammar.Closed]
    | cons token rest =>
      unfold declarations at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact declaration_closed firstAt
      · exact ih tailAt value member

theorem decode_closed {input maximum values}
    (success : decodeBytes input maximum = .ok values) : Grammar.Closed values := by
  obtain ⟨tokens, _, parsed⟩ := decode_has_tokens success
  exact declarations_closed parsed

#print axioms Fang.TptpCandidate.FullFof.term_arguments_within
#print axioms Fang.TptpCandidate.FullFof.term_within
#print axioms Fang.TptpCandidate.FullFof.arguments_within
#print axioms Fang.TptpCandidate.FullFof.atom_within
#print axioms Fang.TptpCandidate.FullFof.term_within_congr
#print axioms Fang.TptpCandidate.FullFof.formula_within_congr
#print axioms Fang.TptpCandidate.FullFof.close_within
#print axioms Fang.TptpCandidate.FullFof.unit_formula_chain_within
#print axioms Fang.TptpCandidate.FullFof.formula_within
#print axioms Fang.TptpCandidate.FullFof.declaration_closed
#print axioms Fang.TptpCandidate.FullFof.declarations_closed
#print axioms Fang.TptpCandidate.FullFof.decode_closed

end Fang.TptpCandidate.FullFof
