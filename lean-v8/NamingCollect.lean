/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The vars collected by the generated naming code are exactly the
   vars of the collected formula, and the argument terms built from them
   are those vars in the same order. -/
import Fof
import NamingResult
import NamingModel
import NnfEntry

-- The step tactics share one rewrite set; not every rewrite applies at every step.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace FangNaming
open Aeneas Aeneas.Std Result fang_fof_core FangScopedFof
open Fang.QuantifiedFOF.BinderRemoval

mutual
/-- Variable `x` occurs in the term. -/
def TermHas (x : Nat) : Fang.Term → Prop
  | .var y => x = y
  | .app _ arguments => TermsHas x arguments
/-- Variable `x` occurs in one of the terms. -/
def TermsHas (x : Nat) : List Fang.Term → Prop
  | [] => False
  | term :: rest => TermHas x term ∨ TermsHas x rest
end

theorem termsHas_iff (x : Nat) (terms : List Fang.Term) : TermsHas x terms ↔ ∃ term ∈ terms, TermHas x term := by
  induction terms with
  | nil => simp [TermsHas]
  | cons head tail ih => simp [TermsHas, ih]

theorem termHas_app (x symbol : Nat) (arguments : List Fang.Term) :
    TermHas x (.app symbol arguments) ↔ ∃ term ∈ arguments, TermHas x term := by
  simp only [TermHas, termsHas_iff]

/-- Variable `x` occurs in the formula. -/
def NnfHas (x : Nat) : Fang.GroundFOF.Nnf → Prop
  | .lit literal => ∃ term ∈ literal.atom.args, TermHas x term
  | .truth | .falsity => False
  | .conj left right | .disj left right => NnfHas x left ∨ NnfHas x right

theorem termWithin_of_has {vars : List Nat} :
    ∀ term : Fang.Term, (∀ x, TermHas x term → x ∈ vars) → Fang.QuantifiedFOF.TermWithin vars term
  | .var y, has => by simpa [Fang.QuantifiedFOF.TermWithin] using has y (by simp [TermHas])
  | .app symbol arguments, has => by
    simp only [Fang.QuantifiedFOF.TermWithin]
    intro term member
    exact termWithin_of_has term (fun x inner => has x ((termHas_app x symbol arguments).mpr ⟨term, member, inner⟩))

theorem groundWithin_of_has {vars : List Nat} :
    ∀ formula : Fang.GroundFOF.Nnf, (∀ x, NnfHas x formula → x ∈ vars) → GroundWithin vars formula
  | .lit _, has => fun term member =>
    termWithin_of_has term (fun x inner => has x ⟨term, member, inner⟩)
  | .truth, _ | .falsity, _ => trivial
  | .conj left right, has | .disj left right, has =>
    ⟨groundWithin_of_has left (fun x inner => has x (Or.inl inner)),
      groundWithin_of_has right (fun x inner => has x (Or.inr inner))⟩

/-- The natural values of a vector of identifiers. -/
def numbers (values : alloc.vec.Vec U32) : List Nat := values.val.map (·.val)

theorem index_eq_ok {α : Type} {values : alloc.vec.Vec α} {index : Usize} {element : α}
    (success : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) values index = ok element) :
    values.val[index.val]? = some element := by
  rw [alloc.vec.Vec.index_slice_index] at success
  simp only [alloc.vec.Vec.index_usize, alloc.vec.Vec.getElem?_Nat_eq] at success
  cases found : values.val[index.val]? with
  | none =>
    simp only [found] at success
    exact absurd success fail_not_ok
  | some value =>
    simp only [found] at success
    rw [ok_eq_ok success]

theorem insert_eq_ok {α : Type} {values : alloc.vec.Vec α} {index : Usize} {element : α}
    {result : alloc.vec.Vec α} (success : alloc.vec.Vec.insert values index element = ok result) :
    result.val = values.val.insertIdx index.val element ∧ index.val < values.val.length := by
  unfold alloc.vec.Vec.insert at success
  split at success
  · rename_i inside
    split at success
    · have same := ok_eq_ok success
      subst same
      exact ⟨by simp, by simpa using inside⟩
    · exact absurd success fail_not_ok
  · exact absurd success fail_not_ok

theorem push_eq_ok {α : Type} {values : alloc.vec.Vec α} {element : α} {result : alloc.vec.Vec α}
    (success : alloc.vec.Vec.push values element = ok result) : result.val = values.val ++ [element] := by
  unfold alloc.vec.Vec.push at success
  dsimp only at success
  split at success
  · have same := ok_eq_ok success
    subst same
    simp
  · exact absurd success fail_not_ok

theorem add_eq_ok {x y z : Usize} (success : (x + y : Result Usize) = ok z) : z.val = x.val + y.val := by
  have equiv := UScalar.add_equiv x y
  rw [success, Result.match.ok] at equiv
  exact equiv.2.1

@[simp] theorem branch_ok {T E : Type} (value : T) :
    core.result.Result.Insts.CoreOpsTry.branch (.Ok value : core.result.Result T E) = ok (.Continue value) := rfl

@[simp] theorem branch_err {T E : Type} (error : E) :
    core.result.Result.Insts.CoreOpsTry.branch (.Err error : core.result.Result T E) = ok (.Break (.Err error)) := rfl

@[simp] theorem residual_err {T E : Type} (error : E) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual T (core.convert.FromSame E)
      (.Err error) = ok (.Err error) := by
  simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
    core.convert.FromSame.from, bind_tc_ok]

theorem numbers_insertIdx {values : List U32} {index : Nat} {element : U32} (inside : index ≤ values.length)
    (x : Nat) : x ∈ (values.insertIdx index element).map (·.val) ↔ x ∈ values.map (·.val) ∨ x = element.val := by
  have perm := (List.perm_insertIdx element values inside).map (·.val)
  rw [perm.mem_iff]
  simp only [List.map_cons, List.mem_cons]
  constructor
  · rintro (same | member)
    · exact Or.inr same
    · exact Or.inl member
  · rintro (member | same)
    · exact Or.inr member
    · exact Or.inl same

theorem numbers_push {values : List U32} {element : U32} (x : Nat) :
    x ∈ (values ++ [element]).map (·.val) ↔ x ∈ values.map (·.val) ∨ x = element.val := by
  simp

set_option hygiene false in
/-- A failed step makes the code return its error, which contradicts completion. -/
macro "residual_absurd" : tactic => `(tactic| (
  simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
  rw [← ok_eq_ok success] at completed
  cases completed))

set_option hygiene false in
/-- A successful allocation, then an insertion before `index` or at the end. -/
macro "insert_case" : tactic => `(tactic| (
  obtain ⟨updated, inserted, success⟩ := bind_eq_ok success
  rw [← ok_eq_ok success]
  obtain ⟨values, inside⟩ := insert_eq_ok inserted
  intro x
  simp only [numbers, values]
  exact numbers_insertIdx (Nat.le_of_lt inside) x))

set_option hygiene false in
/-- A successful push at the end. -/
macro "push_case" : tactic => `(tactic| (
  obtain ⟨updated, pushed, success⟩ := bind_eq_ok success
  rw [← ok_eq_ok success]
  intro x
  simp only [numbers, push_eq_ok pushed]
  exact numbers_push x))

set_option hygiene false in
/-- A successful allocation, then an insertion before `index` or at the end. The test
    of `index` may already be decided by an enclosing split on the same condition. -/
macro "insert_tail" : tactic => `(tactic| (
  obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
  cases answer with
  | Ok _ =>
    simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
    first
    | (split at success
       · insert_case
       · push_case)
    | insert_case
    | push_case
  | Err error => residual_absurd))

set_option hygiene false in
/-- The element at `index` is `id`, so nothing changes. -/
macro "insert_found" : tactic => `(tactic| (
  rw [← ok_eq_ok success]
  intro x
  constructor
  · exact Or.inl
  · rintro (member | same)
    · exact member
    · rename_i equal
      subst same
      rw [← equal]
      exact List.mem_map_of_mem (List.mem_of_getElem? located)))

/-- After a successful insertion, the vector holds the old values and the new one. -/
theorem insert_variable_loop_spec (vars : alloc.vec.Vec U32) (id : U32) (limits : Limits)
    (work : Work) (index : Usize) (result : core.result.Result Unit fang_fof_core.Error × alloc.vec.Vec U32 × Work)
    (success : naming.insert_variable_loop vars id limits work index = ok result)
    (completed : result.1 = .Ok ()) :
    ∀ x, x ∈ numbers result.2.1 ↔ x ∈ numbers vars ∨ x = id.val := by
  unfold naming.insert_variable_loop at success
  dsimp only at success
  split at success
  next inside =>
    have bound : index.val < vars.val.length := by
      simpa [alloc.vec.Vec.len, UScalar.lt_equiv] using inside
    obtain ⟨element, found, success⟩ := bind_eq_ok success
    have located := index_eq_ok found
    split at success
    next smaller =>
      obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
      cases answer with
      | Ok _ =>
        simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
        obtain ⟨next, added, success⟩ := bind_eq_ok success
        have step := add_eq_ok added
        exact insert_variable_loop_spec vars id limits work1 next result success completed
      | Err error => residual_absurd
    next notSmaller =>
      split at success
      next => insert_found
      next => insert_tail
  next outside => insert_tail
termination_by vars.val.length - index.val
decreasing_by
  simp_wf
  simp at step
  omega

theorem insert_variable_spec (vars : alloc.vec.Vec U32) (id : U32) (limits : Limits)
    (work : Work) (result : core.result.Result Unit fang_fof_core.Error × alloc.vec.Vec U32 × Work)
    (success : naming.insert_variable vars id limits work = ok result)
    (completed : result.1 = .Ok ()) :
    ∀ x, x ∈ numbers result.2.1 ↔ x ∈ numbers vars ∨ x = id.val :=
  insert_variable_loop_spec vars id limits work 0#usize result success completed

theorem decodeTerms_eq_map {n : Nat} (terms : Aeneas.Data.ListN.ListN fang.syntax.Term n) :
    decodeTerms terms = terms.toList.map decodeTerm := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp [decodeTerms, Aeneas.Data.ListN.ListN.toList, ih]

theorem decodeVec_eq_map (arguments : alloc.vec.Vec fang.syntax.Term) :
    decodeVec arguments = arguments.val.map decodeTerm := by
  cases arguments with
  | mk slice =>
    cases slice with
    | mk count terms bound =>
      simpa [decodeVec, decodeSlice, alloc.vec.Vec.val, Slice.val] using decodeTerms_eq_map terms

/-- The collected vars of an argument list from `index` on. -/
theorem collect_term_loop_spec (arguments : alloc.vec.Vec fang.syntax.Term) (limits : Limits)
    (child : ∀ i (h : i < arguments.val.length) vars work result,
      naming.collect_term arguments.val[i] vars limits work = ok result → result.1 = .Ok () →
        ∀ x, x ∈ numbers result.2.1 ↔ x ∈ numbers vars ∨ TermHas x (decodeTerm arguments.val[i]))
    (vars : alloc.vec.Vec U32) (work : Work) (index : Usize)
    (result : core.result.Result Unit fang_fof_core.Error × alloc.vec.Vec U32 × Work)
    (success : naming.collect_term_loop arguments vars limits work index = ok result)
    (completed : result.1 = .Ok ()) :
    ∀ x, x ∈ numbers result.2.1 ↔ x ∈ numbers vars ∨
      ∃ j, ∃ h : j < arguments.val.length, index.val ≤ j ∧ TermHas x (decodeTerm arguments.val[j]) := by
  unfold naming.collect_term_loop at success
  dsimp only at success
  split at success
  next inside =>
    have bound : index.val < arguments.val.length := by
      simpa [alloc.vec.Vec.len, UScalar.lt_equiv] using inside
    obtain ⟨term, found, success⟩ := bind_eq_ok success
    have located := index_eq_ok found
    have same : arguments.val[index.val] = term := by
      rw [List.getElem?_eq_getElem bound] at located
      exact Option.some.inj located
    obtain ⟨⟨answer, variables1, work1⟩, collected, success⟩ := bind_eq_ok success
    cases answer with
    | Ok _ =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      obtain ⟨next, added, success⟩ := bind_eq_ok success
      have step := add_eq_ok added
      have first := child index.val bound vars work _ (by rw [same]; exact collected) rfl
      have rest := collect_term_loop_spec arguments limits child variables1 work1 next result success completed
      intro x
      rw [rest x, first x]
      simp only [step] at *
      constructor
      · rintro ((member | has) | ⟨j, h, le, has⟩)
        · exact Or.inl member
        · exact Or.inr ⟨index.val, bound, le_refl _, has⟩
        · exact Or.inr ⟨j, h, by simp at le; omega, has⟩
      · rintro (member | ⟨j, h, le, has⟩)
        · exact Or.inl (Or.inl member)
        · rcases Nat.eq_or_lt_of_le le with equal | later
          · subst equal
            exact Or.inl (Or.inr has)
          · exact Or.inr ⟨j, h, by simp; omega, has⟩
    | Err error => residual_absurd
  next outside =>
    have bound : arguments.val.length ≤ index.val := by
      simpa [alloc.vec.Vec.len, UScalar.lt_equiv] using outside
    rw [← ok_eq_ok success]
    intro x
    constructor
    · exact Or.inl
    · rintro (member | ⟨j, h, le, _⟩)
      · exact member
      · omega
termination_by arguments.val.length - index.val
decreasing_by
  simp_wf
  simp at step
  omega

theorem collect_term_spec {signature : Signature} {scope : VariableScope} (term : fang.syntax.Term)
    (valid : TermValid signature scope term) (limits : Limits) :
    ∀ (vars : alloc.vec.Vec U32) (work : Work)
      (result : core.result.Result Unit fang_fof_core.Error × alloc.vec.Vec U32 × Work),
      naming.collect_term term vars limits work = ok result → result.1 = .Ok () →
      ∀ x, x ∈ numbers result.2.1 ↔ x ∈ numbers vars ∨ TermHas x (decodeTerm term) := by
  induction valid with
  | var id _ =>
    intro vars work result success completed
    unfold naming.collect_term at success
    dsimp only at success
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Ok _ =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      have inserted := insert_variable_spec vars id limits work1 result success completed
      intro x
      rw [inserted x]
      simp [decodeTerm, TermHas]
    | Err error => residual_absurd
  | fun_ symbol arguments _ children ih =>
    intro vars work result success completed
    unfold naming.collect_term at success
    dsimp only at success
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Ok _ =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      have collected := collect_term_loop_spec arguments limits
        (fun i h vars work result success completed => ih i h vars work result success completed)
        vars work1 0#usize result success completed
      intro x
      rw [collected x]
      simp only [decodeTerm, decodeVec_eq_map, termHas_app, List.mem_map]
      constructor
      · rintro (member | ⟨j, h, _, has⟩)
        · exact Or.inl member
        · exact Or.inr ⟨decodeTerm arguments.val[j], ⟨arguments.val[j], List.getElem_mem h, rfl⟩, has⟩
      · rintro (member | ⟨_, ⟨term, member, rfl⟩, has⟩)
        · exact Or.inl member
        · obtain ⟨j, h, rfl⟩ := List.getElem_of_mem member
          exact Or.inr ⟨j, h, Nat.zero_le _, has⟩
    | Err error => residual_absurd

/-- The collected vars of a literal's arguments from `index` on. -/
theorem collect_nnf_loop_spec {signature : Signature} {scope : VariableScope}
    (literal : fang.syntax.Literal) (valid : LiteralScoped signature scope literal) (limits : Limits)
    (vars : alloc.vec.Vec U32) (work : Work) (index : Usize)
    (result : core.result.Result Unit fang_fof_core.Error × alloc.vec.Vec U32 × Work)
    (success : naming.collect_nnf_loop vars limits work literal index = ok result)
    (completed : result.1 = .Ok ()) :
    ∀ x, x ∈ numbers result.2.1 ↔ x ∈ numbers vars ∨
      ∃ j, ∃ h : j < literal.arguments.val.length, index.val ≤ j ∧
        TermHas x (decodeTerm literal.arguments.val[j]) := by
  unfold naming.collect_nnf_loop at success
  dsimp only at success
  split at success
  next inside =>
    have bound : index.val < literal.arguments.val.length := by
      simpa [alloc.vec.Vec.len, UScalar.lt_equiv] using inside
    obtain ⟨term, found, success⟩ := bind_eq_ok success
    have located := index_eq_ok found
    have same : literal.arguments.val[index.val] = term := by
      rw [List.getElem?_eq_getElem bound] at located
      exact Option.some.inj located
    obtain ⟨⟨answer, variables1, work1⟩, collected, success⟩ := bind_eq_ok success
    cases answer with
    | Ok _ =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      obtain ⟨next, added, success⟩ := bind_eq_ok success
      have step := add_eq_ok added
      have first := collect_term_spec term (by rw [← same]; exact valid index.val bound) limits
        vars work _ collected rfl
      have rest := collect_nnf_loop_spec literal valid limits variables1 work1 next result success completed
      intro x
      rw [rest x, first x, ← same]
      simp only [step] at *
      constructor
      · rintro ((member | has) | ⟨j, h, le, has⟩)
        · exact Or.inl member
        · exact Or.inr ⟨index.val, bound, le_refl _, has⟩
        · exact Or.inr ⟨j, h, by simp at le; omega, has⟩
      · rintro (member | ⟨j, h, le, has⟩)
        · exact Or.inl (Or.inl member)
        · rcases Nat.eq_or_lt_of_le le with equal | later
          · subst equal
            exact Or.inl (Or.inr has)
          · exact Or.inr ⟨j, h, by simp; omega, has⟩
    | Err error => residual_absurd
  next outside =>
    have bound : literal.arguments.val.length ≤ index.val := by
      simpa [alloc.vec.Vec.len, UScalar.lt_equiv] using outside
    rw [← ok_eq_ok success]
    intro x
    constructor
    · exact Or.inl
    · rintro (member | ⟨j, h, le, _⟩)
      · exact member
      · omega
termination_by literal.arguments.val.length - index.val
decreasing_by
  simp_wf
  simp at step
  omega

/-- The vars collected from a formula are the old ones and those of the formula. -/
theorem collect_nnf_spec {signature : Signature} {scope : VariableScope} (formula : Nnf)
    (valid : NnfScoped signature scope formula) (limits : Limits) :
    ∀ (vars : alloc.vec.Vec U32) (work : Work)
      (result : core.result.Result Unit fang_fof_core.Error × alloc.vec.Vec U32 × Work),
      naming.collect_nnf formula vars limits work = ok result → result.1 = .Ok () →
      ∀ x, x ∈ numbers result.2.1 ↔ x ∈ numbers vars ∨ NnfHas x (decodeNnf formula) := by
  induction formula with
  | Literal literal =>
    intro vars work result success completed
    unfold naming.collect_nnf at success
    dsimp only at success
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Ok _ =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      have collected := collect_nnf_loop_spec literal valid limits vars work1 0#usize result success completed
      intro x
      rw [collected x]
      simp only [decodeNnf, decodeLiteral, NnfHas, decodeVec_eq_map, List.mem_map]
      constructor
      · rintro (member | ⟨j, h, _, has⟩)
        · exact Or.inl member
        · exact Or.inr ⟨decodeTerm literal.arguments.val[j],
            ⟨literal.arguments.val[j], List.getElem_mem h, rfl⟩, has⟩
      · rintro (member | ⟨_, ⟨term, member, rfl⟩, has⟩)
        · exact Or.inl member
        · obtain ⟨j, h, rfl⟩ := List.getElem_of_mem member
          exact Or.inr ⟨j, h, Nat.zero_le _, has⟩
    | Err error => residual_absurd
  | True | False =>
    intro vars work result success completed
    unfold naming.collect_nnf at success
    dsimp only at success
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Ok _ =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      rw [← ok_eq_ok success]
      intro x
      simp [decodeNnf, NnfHas]
    | Err error => residual_absurd
  | And left right ihl ihr | Or left right ihl ihr =>
    intro vars work result success completed
    unfold naming.collect_nnf at success
    dsimp only at success
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Ok _ =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      obtain ⟨⟨answer1, variables1, work2⟩, collected, success⟩ := bind_eq_ok success
      cases answer1 with
      | Ok _ =>
        simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
        have first := ihl valid.1 vars work1 _ collected rfl
        have second := ihr valid.2 variables1 work2 result success completed
        intro x
        rw [second x, first x]
        simp only [decodeNnf, NnfHas, or_assoc]
      | Err error => residual_absurd
    | Err error => residual_absurd

/-- The argument terms are the vars of the slice from `index` on, appended in order. -/
theorem variable_terms_loop_spec (vars : Slice U32) (limits : Limits) (work : Work)
    (terms : alloc.vec.Vec fang.syntax.Term) (index : Usize)
    (result : core.result.Result (alloc.vec.Vec fang.syntax.Term) fang_fof_core.Error × Work)
    (success : naming.variable_terms_loop vars limits work terms index = ok result) (output)
    (completed : result.1 = .Ok output) :
    output.val = terms.val ++ (vars.val.drop index.val).map fang.syntax.Term.Var := by
  unfold naming.variable_terms_loop at success
  dsimp only at success
  split at success
  next inside =>
    have bound : index.val < vars.val.length := by
      simpa [Slice.len, UScalar.lt_equiv] using inside
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Ok _ =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      obtain ⟨⟨answer1, work2⟩, _, success⟩ := bind_eq_ok success
      cases answer1 with
      | Ok _ =>
        simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
        obtain ⟨element, found, success⟩ := bind_eq_ok success
        obtain ⟨terms1, pushed, success⟩ := bind_eq_ok success
        obtain ⟨next, added, success⟩ := bind_eq_ok success
        have step := add_eq_ok added
        have located : vars.val[index.val]? = some element := by
          unfold Slice.index_usize at found
          split at found
          · exact absurd found fail_not_ok
          · rename_i hit
            simp only [Slice.getElem?_Usize_eq] at hit
            rw [hit, ok_eq_ok found]
        have rest := variable_terms_loop_spec vars limits work2 terms1 next result success output completed
        rw [rest, push_eq_ok pushed, List.append_assoc]
        congr 1
        simp only [step] at *
        rw [List.drop_eq_getElem_cons bound]
        rw [List.getElem?_eq_getElem bound] at located
        rw [Option.some.inj located]
        simp
      | Err error =>
        simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
        rw [← ok_eq_ok success] at completed
        cases completed
    | Err error =>
      simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
      rw [← ok_eq_ok success] at completed
      cases completed
  next outside =>
    have bound : vars.val.length ≤ index.val := by
      simpa [Slice.len, UScalar.lt_equiv] using outside
    have same := ok_eq_ok success
    rw [← same] at completed
    cases completed
    simp [List.drop_eq_nil_of_le bound]
termination_by vars.val.length - index.val
decreasing_by
  simp_wf
  simp at step
  omega

theorem variable_terms_spec (vars : alloc.vec.Vec U32) (limits : Limits) (work : Work)
    (result : core.result.Result (alloc.vec.Vec fang.syntax.Term) fang_fof_core.Error × Work)
    (success : naming.variable_terms (alloc.vec.Vec.deref vars) limits work = ok result) (output)
    (completed : result.1 = .Ok output) :
    decodeVec output = (numbers vars).map Fang.Term.var := by
  have built := variable_terms_loop_spec _ limits work _ 0#usize result success output completed
  rw [decodeVec_eq_map, built]
  simp [alloc.vec.Vec.deref, numbers, decodeTerm]

end FangNaming
