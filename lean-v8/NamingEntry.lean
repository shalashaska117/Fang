/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The public naming entries. A successful `name_nnf` returns the renamed input
   conjoined with every definition in naming order; every model of the input
   extends, on the fresh predicates only, to a model of that formula. A
   successful `name_then_clausify` returns the distributive clauses of it. -/
import NamingRename

-- The step tactics share one rewrite set; not every rewrite applies at every step.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace FangNaming
open Aeneas Aeneas.Std Result fang_fof_core FangScopedFof Fang Fang.QuantifiedFOF.BinderRemoval

/-- The definitions conjoined to the right of a formula, in order. -/
def conjoin (formula : Nnf) (bodies : List Nnf) : Nnf := bodies.foldl Nnf.And formula

/-- The values left in a vector iterator. -/
def iteratorValues {T : Type} (iterator : alloc.vec.into_iter.IntoIter T) : List T :=
  alloc.vec.Vec.val iterator

theorem next_eq_ok {T : Type} {iterator : alloc.vec.into_iter.IntoIter T}
    {result : Option T × alloc.vec.into_iter.IntoIter T}
    (success : alloc.vec.into_iter.IteratorIntoIter.next iterator = ok result) :
    (result.1 = none ∧ iteratorValues iterator = []) ∨
      ∃ head tail, iteratorValues iterator = head :: tail ∧ result.1 = some head ∧
        iteratorValues result.2 = tail := by
  unfold alloc.vec.into_iter.IteratorIntoIter.next at success
  split at success
  · rename_i empty
    left
    rw [← ok_eq_ok success]
    exact ⟨rfl, empty⟩
  · rename_i head tail split
    right
    rw [← ok_eq_ok success]
    exact ⟨head, tail, split, rfl, by simp [iteratorValues]⟩

theorem name_nnf_loop_spec (iterator : alloc.vec.into_iter.IntoIter Nnf) (combined output : Nnf)
    (success : naming.name_nnf_loop iterator combined = ok output) :
    output = conjoin combined (iteratorValues iterator) := by
  unfold naming.name_nnf_loop at success
  obtain ⟨⟨option, rest⟩, stepped, success⟩ := bind_eq_ok success
  rcases next_eq_ok stepped with ⟨isNone, empty⟩ | ⟨head, tail, split, isSome, remaining⟩
  · dsimp only at isNone
    simp only [Aeneas.Std.uncurry, isNone] at success
    rw [← ok_eq_ok success, empty]
    rfl
  · dsimp only at isSome remaining
    simp only [Aeneas.Std.uncurry, isSome] at success
    rw [name_nnf_loop_spec rest _ output success, split, remaining]
    rfl
termination_by (iteratorValues iterator).length
decreasing_by
  rw [remaining, split]
  simp

theorem conjoin_holds {D : Type} (model : Interpretation D) (valuation : Nat → D) (formula : Nnf) :
    ∀ bodies : List Nnf, (decodeNnf (conjoin formula bodies)).Holds model valuation ↔
      (decodeNnf formula).Holds model valuation ∧ ∀ body ∈ bodies, (decodeNnf body).Holds model valuation := by
  intro bodies
  induction bodies generalizing formula with
  | nil => simp [conjoin]
  | cons head tail ih =>
    simp only [conjoin, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [decodeNnf, Fang.GroundFOF.Nnf.Holds, List.mem_cons, forall_eq_or_imp]
    tauto

theorem conjoin_below (bound : Nat) (formula : Nnf) :
    ∀ bodies : List Nnf, PredsBelow bound (decodeNnf formula) →
      (∀ body ∈ bodies, PredsBelow bound (decodeNnf body)) → PredsBelow bound (decodeNnf (conjoin formula bodies)) := by
  intro bodies
  induction bodies generalizing formula with
  | nil => intro below _; simpa [conjoin] using below
  | cons head tail ih =>
    intro below rest
    simp only [conjoin, List.foldl_cons] at ih ⊢
    exact ih _ ⟨below, rest head List.mem_cons_self⟩ (fun body member => rest body (List.mem_cons_of_mem _ member))

theorem conjoin_scoped {signature : Signature} {scope : VariableScope} (formula : Nnf) :
    ∀ bodies : List Nnf, NnfScoped signature scope formula →
      (∀ body ∈ bodies, NnfScoped signature scope body) → NnfScoped signature scope (conjoin formula bodies) := by
  intro bodies
  induction bodies generalizing formula with
  | nil => intro valid _; simpa [conjoin] using valid
  | cons head tail ih =>
    intro valid rest
    simp only [conjoin, List.foldl_cons] at ih ⊢
    exact ih _ ⟨valid, rest head List.mem_cons_self⟩ (fun body member => rest body (List.mem_cons_of_mem _ member))

theorem definitions_below {base : Nat} {definitions : List Fang.GroundFOF.Nnf}
    (valid : Definitions base definitions) : ∀ formula ∈ definitions, PredsBelow (base + definitions.length) formula := by
  intro formula member
  obtain ⟨j, h, rfl⟩ := List.getElem_of_mem member
  obtain ⟨vars, body, equation, _, below⟩ := valid j h
  rw [equation]
  exact ⟨show base + j < base + definitions.length by omega, predsBelow_mono (by omega) body below⟩

theorem bounded_add_eq_ok {left right cap : Usize} {kind : Resource} {answer : core.result.Result Usize fang_fof_core.Error}
    (success : bounded_add left right cap kind = ok answer) (value : Usize) (completed : answer = .Ok value) :
    value.val = left.val + right.val := by
  unfold bounded_add at success
  try dsimp only at success
  split at success
  · rw [← ok_eq_ok success] at completed
    cases completed
  · obtain ⟨room, _, success⟩ := bind_eq_ok success
    split at success
    · rw [← ok_eq_ok success] at completed
      cases completed
    · obtain ⟨sum, added, success⟩ := bind_eq_ok success
      rw [← ok_eq_ok success] at completed
      simp only [core.result.Result.Ok.injEq] at completed
      subst completed
      exact add_eq_ok added

/-- The meaning of a successful renaming of a block formula. -/
theorem name_nnf_spec {signature : Signature} {scope : VariableScope} (formula : Nnf) (threshold : Usize)
    (next : U32) (limits : Limits) (statistics : Statistics) (output : naming.Renamed)
    (valid : NnfScoped signature scope formula) (below : PredsBelow next.val (decodeNnf formula))
    (success : naming.name_nnf formula threshold next limits statistics = ok (.Ok output)) :
    next.val ≤ output.next.val ∧
      NnfScoped signature scope output.formula ∧
      PredsBelow output.next.val (decodeNnf output.formula) ∧
      ∀ {D : Type} [Nonempty D] (model : Interpretation D), (∀ valuation, (decodeNnf formula).Holds model valuation) →
        ∃ extended : Interpretation D, AgreeBelow next.val model extended ∧
          ∀ valuation, (decodeNnf output.formula).Holds extended valuation := by
  unfold naming.name_nnf at success
  try dsimp only at success
  obtain ⟨answer, _, success⟩ := bind_eq_ok success
  cases answer with
  | Err error =>
    simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
    cases ok_eq_ok success
  | Ok _ =>
    simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
    obtain ⟨answer1, _, success⟩ := bind_eq_ok success
    cases answer1 with
    | Err error =>
      simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
      cases ok_eq_ok success
    | Ok _ =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      obtain ⟨⟨answer2, renamer⟩, renamedCall, success⟩ := bind_eq_ok success
      cases answer2 with
      | Err error =>
        simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
        cases ok_eq_ok success
      | Ok pair =>
        obtain ⟨renamed, count⟩ := pair
        simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
        have post := rename_spec limits formula _ _ renamed count valid below renamedCall rfl
        obtain ⟨new, bodiesAfter, nextAfter, _, scopedRenamed, scopedNew, definitions, belowRenamed, _,
          meaning⟩ := post
        simp only [alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] at bodiesAfter
        obtain ⟨answer3, _, success⟩ := bind_eq_ok success
        cases answer3 with
        | Err error =>
          simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
          cases ok_eq_ok success
        | Ok _ =>
          simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
          obtain ⟨⟨answer4, work⟩, _, success⟩ := bind_eq_ok success
          cases answer4 with
          | Err error =>
            simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
            cases ok_eq_ok success
          | Ok _ =>
            simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
            obtain ⟨iterator, converted, success⟩ := bind_eq_ok success
            obtain ⟨combined, looped, success⟩ := bind_eq_ok success
            have same := ok_eq_ok success
            simp only [core.result.Result.Ok.injEq] at same
            subst same
            have values : iteratorValues iterator = new := by
              unfold alloc.vec.IntoIteratorVec.into_iter at converted
              rw [← ok_eq_ok converted]
              exact bodiesAfter
            have formulaEq : combined = conjoin renamed new := by
              rw [name_nnf_loop_spec iterator renamed combined looped, values]
            simp only [formulaEq]
            refine ⟨by simp only at nextAfter; omega, conjoin_scoped _ _ scopedRenamed scopedNew,
              conjoin_below _ _ _ belowRenamed ?_, ?_⟩
            · intro body member
              have below := definitions_below definitions (decodeNnf body) (List.mem_map_of_mem member)
              simp only [List.length_map] at below
              simpa [nextAfter] using below
            · intro D _ model holds
              refine ⟨extend model (new.map decodeNnf), extend_agree model definitions, fun valuation => ?_⟩
              rw [conjoin_holds]
              exact ⟨(meaning model valuation).mpr (holds valuation),
                fun body member => extend_definitions_hold model definitions _ (List.mem_map_of_mem member) valuation⟩

/-- Every literal of the distributive clauses uses a predicate of the formula. -/
theorem clauses_below (bound : Nat) :
    ∀ formula : Fang.GroundFOF.Nnf, PredsBelow bound formula →
      ∀ clause ∈ formula.clauses, ∀ literal ∈ clause, literal.atom.pred < bound
  | .lit literal, below, clause, member, other, inside => by
    simp only [Fang.GroundFOF.Nnf.clauses, List.mem_singleton] at member
    subst member
    simp only [List.mem_singleton] at inside
    subst inside
    exact below
  | .truth, _, _, member, _, _ => by simp [Fang.GroundFOF.Nnf.clauses] at member
  | .falsity, _, clause, member, _, inside => by
    simp only [Fang.GroundFOF.Nnf.clauses, List.mem_singleton] at member
    subst member
    cases inside
  | .conj left right, below, clause, member, literal, inside => by
    simp only [Fang.GroundFOF.Nnf.clauses, List.mem_append] at member
    rcases member with member | member
    · exact clauses_below bound left below.1 clause member literal inside
    · exact clauses_below bound right below.2 clause member literal inside
  | .disj left right, below, clause, member, literal, inside => by
    simp only [Fang.GroundFOF.Nnf.clauses, Fang.GroundFOF.clauseProduct, List.mem_flatMap, List.mem_map] at member
    obtain ⟨first, firstMember, second, secondMember, rfl⟩ := member
    rcases List.mem_append.mp inside with inner | inner
    · exact clauses_below bound left below.1 first firstMember literal inner
    · exact clauses_below bound right below.2 second secondMember literal inner

/-- The clauses of a successful `name_then_clausify`: their predicates are below the
    returned `next`, and every model of the input extends, on the fresh predicates
    only, to a model of them. -/
theorem name_then_clausify_spec {signature : Signature} {scope : VariableScope} (formula : Nnf)
    (threshold : Usize) (next : U32) (limits : Limits) (statistics : Statistics) (output : naming.Named)
    (valid : NnfScoped signature scope formula) (below : PredsBelow next.val (decodeNnf formula))
    (success : naming.name_then_clausify formula threshold next limits statistics = ok (.Ok output)) :
    next.val ≤ output.next.val ∧
      (∀ clause ∈ decodeClauses output.clauses.val, ∀ literal ∈ clause, literal.atom.pred < output.next.val) ∧
      ∀ {D : Type} [Nonempty D] (model : Interpretation D), (∀ valuation, (decodeNnf formula).Holds model valuation) →
        ∃ extended : Interpretation D, AgreeBelow next.val model extended ∧
          (decodeClauses output.clauses.val).Models extended := by
  unfold naming.name_then_clausify at success
  try dsimp only at success
  obtain ⟨answer, renamedCall, success⟩ := bind_eq_ok success
  cases answer with
  | Err error =>
    simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
    cases ok_eq_ok success
  | Ok renamed =>
    simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
    obtain ⟨answer1, clausified, success⟩ := bind_eq_ok success
    cases answer1 with
    | Err error =>
      simp only [Aeneas.Std.uncurry, branch_err, bind_tc_ok, bind_ok, residual_err] at success
      cases ok_eq_ok success
    | Ok clauses =>
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      have same := ok_eq_ok success
      simp only [core.result.Result.Ok.injEq] at same
      subst same
      obtain ⟨grows, scopedNamed, belowNamed, meaning⟩ :=
        name_nnf_spec formula threshold next limits statistics renamed valid below renamedCall
      have exact := (clausify_nnf_from_success renamed.formula signature scope scopedNamed limits statistics clauses
        clausified).2.2.1
      refine ⟨grows, ?_, ?_⟩
      · simp only [exact]
        exact clauses_below _ _ belowNamed
      · intro D _ model holds
        obtain ⟨extended, agree, models⟩ := meaning model holds
        exact ⟨extended, agree, (clausify_nnf_from_models renamed.formula signature scope scopedNamed limits statistics
          clauses clausified extended).mpr models⟩

end FangNaming
