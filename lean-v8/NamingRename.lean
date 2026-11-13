/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   What a successful run of the generated renaming code produces: the renamed
   formula, the definitions it appended in naming order with consecutive fresh
   predicates, and the meaning of the renamed formula under the interpretation
   extended by those definitions, which is the meaning of the input. -/
import NamingCollect
import NnfEntry

-- The step tactics share one rewrite set; not every rewrite applies at every step.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace FangNaming
open Aeneas Aeneas.Std Aeneas.Std.WP Result fang_fof_core FangScopedFof Fang Fang.QuantifiedFOF.BinderRemoval

theorem spec_eq_ok {α : Type} {m : Result α} {post : α → Prop} (holds : spec m post) {value : α}
    (success : m = ok value) : post value := by
  rw [success] at holds
  simpa using holds

/-- Every variable of a scoped formula is valid in its scope; validity depends on the value only. -/
theorem termHas_valid {signature : Signature} {scope : VariableScope} {term : fang.syntax.Term}
    (valid : TermValid signature scope term) :
    ∀ x, TermHas x (decodeTerm term) → ∀ id : U32, id.val = x → VariableValid scope id := by
  induction valid with
  | var id inScope =>
    intro x has other same
    simp only [decodeTerm, TermHas] at has
    cases scope with
    | Ground => exact absurd inScope (by simp [VariableValid])
    | Bound count =>
      simp only [VariableValid] at inScope ⊢
      omega
  | fun_ symbol arguments _ children ih =>
    intro x has other same
    simp only [decodeTerm, decodeVec_eq_map, termHas_app, List.mem_map] at has
    obtain ⟨_, ⟨term, member, rfl⟩, inner⟩ := has
    obtain ⟨j, h, rfl⟩ := List.getElem_of_mem member
    exact ih j h x inner other same

theorem nnfHas_valid {signature : Signature} {scope : VariableScope} :
    ∀ formula : Nnf, NnfScoped signature scope formula →
      ∀ x, NnfHas x (decodeNnf formula) → ∀ id : U32, id.val = x → VariableValid scope id
  | .Literal literal, valid, x, has, id, same => by
    simp only [decodeNnf, decodeLiteral, NnfHas, decodeVec_eq_map, List.mem_map] at has
    obtain ⟨_, ⟨term, member, rfl⟩, inner⟩ := has
    obtain ⟨j, h, rfl⟩ := List.getElem_of_mem member
    exact termHas_valid (valid j h) x inner id same
  | .True, _, _, has, _, _ | .False, _, _, has, _, _ => by simp [decodeNnf, NnfHas] at has
  | .And left right, valid, x, has, id, same | .Or left right, valid, x, has, id, same => by
    simp only [decodeNnf, NnfHas] at has
    rcases has with inner | inner
    · exact nnfHas_valid left valid.1 x inner id same
    · exact nnfHas_valid right valid.2 x inner id same

/-- A literal over vars of a scoped formula is scoped. -/
theorem variables_scoped {signature : Signature} {scope : VariableScope} {body : Nnf}
    (valid : NnfScoped signature scope body) (vars : alloc.vec.Vec U32)
    (inside : ∀ x, x ∈ numbers vars → NnfHas x (decodeNnf body)) (positive : Bool) (predicate : U32)
    (terms : alloc.vec.Vec fang.syntax.Term) (values : terms.val = vars.val.map fang.syntax.Term.Var) :
    NnfScoped signature scope (.Literal ⟨positive, predicate, terms⟩) := by
  intro i h
  have hv : i < vars.val.length := by simpa [values] using h
  simp only [values, List.getElem_map]
  apply TermValid.var
  exact nnfHas_valid body valid _ (inside _ (List.mem_map_of_mem (List.getElem_mem hv))) _ rfl

theorem variable_terms_values (vars : alloc.vec.Vec U32) (limits : Limits) (work : Work)
    (result : core.result.Result (alloc.vec.Vec fang.syntax.Term) fang_fof_core.Error × Work)
    (success : naming.variable_terms (alloc.vec.Vec.deref vars) limits work = ok result) (output)
    (completed : result.1 = .Ok output) :
    output.val = vars.val.map fang.syntax.Term.Var := by
  have built := variable_terms_loop_spec _ limits work _ 0#usize result success output completed
  rw [built]
  simp [alloc.vec.Vec.deref]

theorem checked_add_eq_some {x y z : U32} (checked : U32.checked_add x y = some z) : z.val = x.val + y.val := by
  have spec := U32.checked_add_bv_spec x y
  rw [checked] at spec
  exact spec.2.1

/-- One naming step: a fresh atom over the vars of the body, and its definition appended. -/
theorem name_spec {signature : Signature} {scope : VariableScope} (self : naming.Renamer) (body : Nnf)
    (valid : NnfScoped signature scope body) (limits : Limits)
    (result : core.result.Result Nnf fang_fof_core.Error × naming.Renamer)
    (success : naming.Renamer.name self body limits = ok result) (atom : Nnf)
    (completed : result.1 = .Ok atom) :
    ∃ vars : List Nat,
      result.2.next.val = self.next.val + 1 ∧ result.2.threshold = self.threshold ∧
      (∃ guard, result.2.bodies.val = self.bodies.val ++ [guard] ∧
        decodeNnf guard = .disj (.lit ⟨false, ⟨self.next.val, vars.map Term.var⟩⟩) (decodeNnf body) ∧
        NnfScoped signature scope guard) ∧
      decodeNnf atom = .lit ⟨true, ⟨self.next.val, vars.map Term.var⟩⟩ ∧
      NnfScoped signature scope atom ∧
      (∀ x, x ∈ vars ↔ NnfHas x (decodeNnf body)) := by
  unfold naming.Renamer.name at success
  dsimp only at success
  obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
  cases answer with
  | Err error => residual_absurd
  | Ok _ =>
    simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
    obtain ⟨option, lifted, success⟩ := bind_eq_ok success
    simp only [lift] at lifted
    have option_eq := (ok_eq_ok lifted).symm
    obtain ⟨answer1, converted, success⟩ := bind_eq_ok success
    cases option with
    | none =>
      simp only [core.option.Option.ok_or] at converted
      have same := ok_eq_ok converted
      subst same
      residual_absurd
    | some next =>
      simp only [core.option.Option.ok_or] at converted
      have same := ok_eq_ok converted
      subst same
      simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
      have next_val := checked_add_eq_some option_eq.symm
      obtain ⟨⟨answer2, vars, work2⟩, collected, success⟩ := bind_eq_ok success
      cases answer2 with
      | Err error => residual_absurd
      | Ok _ =>
        simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
        have members := collect_nnf_spec body valid limits _ work1 _ collected rfl
        obtain ⟨⟨answer3, work3⟩, built, success⟩ := bind_eq_ok success
        cases answer3 with
        | Err error => residual_absurd
        | Ok atomTerms =>
          simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
          obtain ⟨⟨answer4, work4⟩, built2, success⟩ := bind_eq_ok success
          cases answer4 with
          | Err error => residual_absurd
          | Ok guardTerms =>
            simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
            obtain ⟨⟨answer5, work5⟩, _, success⟩ := bind_eq_ok success
            cases answer5 with
            | Err error => residual_absurd
            | Ok _ =>
              simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success
              obtain ⟨bodies, pushed, success⟩ := bind_eq_ok success
              obtain ⟨definitions, _, success⟩ := bind_eq_ok success
              rw [← ok_eq_ok success] at completed ⊢
              simp only [core.result.Result.Ok.injEq] at completed
              subst completed
              have empty : numbers (alloc.vec.Vec.new U32) = [] := by simp [numbers]
              have exact : ∀ x, x ∈ numbers vars ↔ NnfHas x (decodeNnf body) := by
                intro x
                rw [members x, empty]
                simp
              have atomValues := variable_terms_values vars limits work2 _ built atomTerms rfl
              have guardValues := variable_terms_values vars limits work3 _ built2 guardTerms rfl
              have atomDecoded : decodeVec atomTerms = (numbers vars).map Term.var := by
                rw [decodeVec_eq_map, atomValues]
                simp [numbers, decodeTerm]
              have guardDecoded : decodeVec guardTerms = (numbers vars).map Term.var := by
                rw [decodeVec_eq_map, guardValues]
                simp [numbers, decodeTerm]
              refine ⟨numbers vars, by simp [next_val], rfl, ⟨_, push_eq_ok pushed, ?_, ?_⟩, ?_, ?_, exact⟩
              · simp [decodeNnf, decodeLiteral, guardDecoded]
              · exact ⟨variables_scoped valid vars (fun x member => (exact x).mp member) false self.next
                  guardTerms guardValues, valid⟩
              · simp [decodeNnf, decodeLiteral, atomDecoded]
              · exact variables_scoped valid vars (fun x member => (exact x).mp member) true self.next
                  atomTerms atomValues

/-- What renaming `formula` into `renamed` did, from a state with `bodies` and `next` to `after`. -/
def RenamePost (signature : Signature) (scope : VariableScope) (bodies : List Nnf) (next : Nat)
    (threshold : Usize) (formula renamed : Nnf) (after : naming.Renamer) : Prop :=
  ∃ new : List Nnf,
    after.bodies.val = bodies ++ new ∧
    after.next.val = next + new.length ∧
    after.threshold = threshold ∧
    NnfScoped signature scope renamed ∧ (∀ body ∈ new, NnfScoped signature scope body) ∧
    Definitions next (new.map decodeNnf) ∧
    PredsBelow after.next.val (decodeNnf renamed) ∧
    (∀ x, NnfHas x (decodeNnf renamed) ↔ NnfHas x (decodeNnf formula)) ∧
    ∀ {D : Type} [Nonempty D] (model : Interpretation D) valuation,
      (decodeNnf renamed).Holds (extend model (new.map decodeNnf)) valuation ↔
        (decodeNnf formula).Holds model valuation

theorem post_copy {signature : Signature} {scope : VariableScope} {formula : Nnf}
    (valid : NnfScoped signature scope formula) {after : naming.Renamer} {bodies : List Nnf} {next : Nat}
    {threshold : Usize} (sameBodies : after.bodies.val = bodies) (sameNext : after.next.val = next)
    (sameThreshold : after.threshold = threshold) (below : PredsBelow next (decodeNnf formula)) :
    RenamePost signature scope bodies next threshold formula formula after := by
  refine ⟨[], by simp [sameBodies], by simp [sameNext], sameThreshold, valid, by simp, ?_, ?_, fun x => Iff.rfl, ?_⟩
  · simpa using definitions_nil next
  · rw [sameNext]; exact below
  · intro D _ model valuation
    simp [extend_nil]

/-- Both sides of a binary node, renamed one after the other, keep their meaning together. -/
theorem pair_semantics {D : Type} [Nonempty D] (model : Interpretation D) (valuation : Nat → D)
    {base : Nat} {first second : List Fang.GroundFOF.Nnf} {left left' right right' : Fang.GroundFOF.Nnf}
    (valid : Definitions base (first ++ second))
    (belowLeft : PredsBelow (base + first.length) left') (belowRight : PredsBelow base right)
    (meaningLeft : left'.Holds (extend model first) valuation ↔ left.Holds model valuation)
    (meaningRight : right'.Holds (extend (extend model first) second) valuation ↔
      right.Holds (extend model first) valuation) :
    (left'.Holds (extend model (first ++ second)) valuation ↔ left.Holds model valuation) ∧
      (right'.Holds (extend model (first ++ second)) valuation ↔ right.Holds model valuation) := by
  obtain ⟨validFirst, _⟩ := definitions_append.mp valid
  constructor
  · rw [← holds_agreeBelow (extend_append_agree model valid) valuation left' belowLeft]
    exact meaningLeft
  · rw [extend_append, meaningRight]
    exact (holds_agreeBelow (extend_agree model validFirst) valuation right belowRight).symm

theorem post_pair {signature : Signature} {scope : VariableScope} {bodies : List Nnf} {next : Nat}
    {threshold : Usize} {left right left' right' : Nnf} {middle after : naming.Renamer}
    (postLeft : RenamePost signature scope bodies next threshold left left' middle)
    (postRight : RenamePost signature scope middle.bodies.val middle.next.val middle.threshold right right' after)
    (belowRight : PredsBelow next (decodeNnf right)) :
    ∃ new : List Nnf,
      after.bodies.val = bodies ++ new ∧ after.next.val = next + new.length ∧ after.threshold = threshold ∧
      NnfScoped signature scope left' ∧ NnfScoped signature scope right' ∧
      (∀ body ∈ new, NnfScoped signature scope body) ∧ Definitions next (new.map decodeNnf) ∧
      PredsBelow after.next.val (decodeNnf left') ∧ PredsBelow after.next.val (decodeNnf right') ∧
      (∀ x, NnfHas x (decodeNnf left') ↔ NnfHas x (decodeNnf left)) ∧
      (∀ x, NnfHas x (decodeNnf right') ↔ NnfHas x (decodeNnf right)) ∧
      ∀ {D : Type} [Nonempty D] (model : Interpretation D) valuation,
        ((decodeNnf left').Holds (extend model (new.map decodeNnf)) valuation ↔
          (decodeNnf left).Holds model valuation) ∧
        ((decodeNnf right').Holds (extend model (new.map decodeNnf)) valuation ↔
          (decodeNnf right).Holds model valuation) := by
  obtain ⟨first, bodies1, next1, threshold1, scopedLeft, scopedFirst, validFirst, belowLeft', hasLeft,
    meaningLeft⟩ := postLeft
  obtain ⟨second, bodies2, next2, threshold2, scopedRight, scopedSecond, validSecond, belowRight', hasRight,
    meaningRight⟩ := postRight
  have valid : Definitions next ((first ++ second).map decodeNnf) := by
    rw [List.map_append, definitions_append]
    exact ⟨validFirst, by simpa [next1] using validSecond⟩
  refine ⟨first ++ second, by rw [bodies2, bodies1, List.append_assoc], by rw [next2, next1]; simp; omega,
    by rw [threshold2, threshold1], scopedLeft, scopedRight, ?_, valid, ?_, belowRight', hasLeft, hasRight, ?_⟩
  · intro body member
    rcases List.mem_append.mp member with inner | inner
    · exact scopedFirst body inner
    · exact scopedSecond body inner
  · exact predsBelow_mono (by rw [next2]; omega) _ belowLeft'
  · intro D _ model valuation
    rw [List.map_append]
    exact pair_semantics model valuation (by rwa [← List.map_append])
      (by rw [List.length_map, ← next1]; exact belowLeft') belowRight
      (meaningLeft model valuation) (meaningRight (extend model (first.map decodeNnf)) valuation)

theorem post_and {signature : Signature} {scope : VariableScope} {bodies : List Nnf} {next : Nat}
    {threshold : Usize} {left right left' right' : Nnf} {middle after : naming.Renamer}
    (postLeft : RenamePost signature scope bodies next threshold left left' middle)
    (postRight : RenamePost signature scope middle.bodies.val middle.next.val middle.threshold right right' after)
    (belowRight : PredsBelow next (decodeNnf right)) :
    RenamePost signature scope bodies next threshold (.And left right) (.And left' right') after := by
  obtain ⟨new, bodies1, next1, threshold1, scopedLeft, scopedRight, scopedNew, valid, belowLeft, belowRight',
    hasLeft, hasRight, meaning⟩ := post_pair postLeft postRight belowRight
  refine ⟨new, bodies1, next1, threshold1, ⟨scopedLeft, scopedRight⟩, scopedNew, valid,
    ⟨belowLeft, belowRight'⟩, ?_, ?_⟩
  · intro x
    simp only [decodeNnf, NnfHas, hasLeft, hasRight]
  · intro D _ model valuation
    simp only [decodeNnf, Fang.GroundFOF.Nnf.Holds]
    exact and_congr (meaning model valuation).1 (meaning model valuation).2

theorem post_or {signature : Signature} {scope : VariableScope} {bodies : List Nnf} {next : Nat}
    {threshold : Usize} {left right left' right' : Nnf} {middle after : naming.Renamer}
    (postLeft : RenamePost signature scope bodies next threshold left left' middle)
    (postRight : RenamePost signature scope middle.bodies.val middle.next.val middle.threshold right right' after)
    (belowRight : PredsBelow next (decodeNnf right)) :
    RenamePost signature scope bodies next threshold (.Or left right) (.Or left' right') after := by
  obtain ⟨new, bodies1, next1, threshold1, scopedLeft, scopedRight, scopedNew, valid, belowLeft, belowRight',
    hasLeft, hasRight, meaning⟩ := post_pair postLeft postRight belowRight
  refine ⟨new, bodies1, next1, threshold1, ⟨scopedLeft, scopedRight⟩, scopedNew, valid,
    ⟨belowLeft, belowRight'⟩, ?_, ?_⟩
  · intro x
    simp only [decodeNnf, NnfHas, hasLeft, hasRight]
  · intro D _ model valuation
    simp only [decodeNnf, Fang.GroundFOF.Nnf.Holds]
    exact or_congr (meaning model valuation).1 (meaning model valuation).2

/-- Naming one side after both sides were renamed. `named` is the renamed side that
    becomes a definition, `kept` the other one; `swap` puts them back in order. -/
theorem post_named {signature : Signature} {scope : VariableScope} {bodies : List Nnf} {next : Nat}
    {threshold : Usize} {left right left' right' : Nnf} {middle after final : naming.Renamer}
    (postLeft : RenamePost signature scope bodies next threshold left left' middle)
    (postRight : RenamePost signature scope middle.bodies.val middle.next.val middle.threshold right right' after)
    (belowRight : PredsBelow next (decodeNnf right))
    (nameLeft : Bool) (atom : Nnf) (vars : List Nat)
    (nextFinal : final.next.val = after.next.val + 1) (thresholdFinal : final.threshold = after.threshold)
    (guard : Nnf) (bodiesFinal : final.bodies.val = after.bodies.val ++ [guard])
    (guardDecoded : decodeNnf guard = .disj (.lit ⟨false, ⟨after.next.val, vars.map Term.var⟩⟩)
      (decodeNnf (if nameLeft then left' else right')))
    (guardScoped : NnfScoped signature scope guard)
    (atomDecoded : decodeNnf atom = .lit ⟨true, ⟨after.next.val, vars.map Term.var⟩⟩)
    (atomScoped : NnfScoped signature scope atom)
    (exact : ∀ x, x ∈ vars ↔ NnfHas x (decodeNnf (if nameLeft then left' else right'))) :
    RenamePost signature scope bodies next threshold (.Or left right)
      (if nameLeft then .Or atom right' else .Or left' atom) final := by
  obtain ⟨new, bodies1, next1, threshold1, scopedLeft, scopedRight, scopedNew, valid, belowLeft, belowRight',
    hasLeft, hasRight, meaning⟩ := post_pair postLeft postRight belowRight
  have namedBelow : PredsBelow after.next.val (decodeNnf (if nameLeft then left' else right')) := by
    cases nameLeft <;> simpa using (by assumption)
  have definition : Definition (next + new.length) (decodeNnf guard) := by
    rw [guardDecoded, ← next1]
    exact ⟨vars, _, rfl, groundWithin_of_has _ (fun x has => (exact x).mpr has), namedBelow⟩
  have validAll : Definitions next ((new ++ [guard]).map decodeNnf) := by
    rw [List.map_append, definitions_append]
    exact ⟨valid, by simpa using definitions_singleton.mpr definition⟩
  -- The atom means the named side, before and after the definition is added.
  have atomMeaning : ∀ {D : Type} [Nonempty D] (model : Interpretation D) valuation,
      (decodeNnf atom).Holds (extend model ((new ++ [guard]).map decodeNnf)) valuation ↔
        (decodeNnf (if nameLeft then left' else right')).Holds (extend model (new.map decodeNnf)) valuation := by
    intro D _ model valuation
    rw [List.map_append, List.map_singleton, extend_snoc, atomDecoded, guardDecoded]
    exact extendOne_atom _ _ vars _ (groundWithin_of_has _ (fun x has => (exact x).mpr has)) valuation
  have keptMeaning : ∀ {D : Type} [Nonempty D] (model : Interpretation D) valuation (side : Nnf),
      PredsBelow after.next.val (decodeNnf side) →
      ((decodeNnf side).Holds (extend model ((new ++ [guard]).map decodeNnf)) valuation ↔
        (decodeNnf side).Holds (extend model (new.map decodeNnf)) valuation) := by
    intro D _ model valuation side below
    have agree := extendOne_agree definition (extend model (new.map decodeNnf))
    rw [List.map_append, List.map_singleton, extend_snoc]
    rw [next1] at below
    exact (holds_agreeBelow agree valuation _ below).symm
  refine ⟨new ++ [guard], by rw [bodiesFinal, bodies1, List.append_assoc], by rw [nextFinal, next1]; simp; omega,
    by rw [thresholdFinal, threshold1], ?_, ?_, validAll, ?_, ?_, ?_⟩
  · cases nameLeft
    · exact ⟨scopedLeft, atomScoped⟩
    · exact ⟨atomScoped, scopedRight⟩
  · intro body member
    rcases List.mem_append.mp member with inner | inner
    · exact scopedNew body inner
    · rw [List.mem_singleton] at inner
      subst inner
      exact guardScoped
  · have atomBelow : PredsBelow final.next.val (decodeNnf atom) := by
      rw [atomDecoded, nextFinal]
      show after.next.val < after.next.val + 1
      omega
    cases nameLeft
    · exact ⟨predsBelow_mono (by omega) _ belowLeft, atomBelow⟩
    · exact ⟨atomBelow, predsBelow_mono (by omega) _ belowRight'⟩
  · intro x
    have atomHas : NnfHas x (decodeNnf atom) ↔ x ∈ vars := by
      rw [atomDecoded]
      simp [NnfHas, TermHas, List.mem_map]
    cases nameLeft
    · simp only [decodeNnf, NnfHas, Bool.false_eq_true, ↓reduceIte] at exact ⊢
      rw [atomHas, exact, hasLeft, hasRight]
    · simp only [decodeNnf, NnfHas, ↓reduceIte] at exact ⊢
      rw [atomHas, exact, hasLeft, hasRight]
  · intro D _ model valuation
    have both := meaning model valuation
    have atomHolds := atomMeaning model valuation
    cases nameLeft
    · simp only [Bool.false_eq_true, ↓reduceIte] at atomHolds ⊢
      simp only [decodeNnf, Fang.GroundFOF.Nnf.Holds]
      rw [keptMeaning model valuation left' belowLeft, atomHolds]
      exact or_congr both.1 both.2
    · simp only [↓reduceIte] at atomHolds ⊢
      simp only [decodeNnf, Fang.GroundFOF.Nnf.Holds]
      rw [keptMeaning model valuation right' belowRight', atomHolds]
      exact or_congr both.1 both.2

set_option hygiene false in
/-- Step over a successful counter update or recursive call whose answer is case split. -/
macro "step_ok" : tactic => `(tactic| simp only [Aeneas.Std.uncurry, branch_ok, bind_tc_ok, bind_ok] at success)

theorem rename_spec {signature : Signature} {scope : VariableScope} (limits : Limits) :
    ∀ (formula : Nnf) (self : naming.Renamer)
      (result : core.result.Result (Nnf × Usize) fang_fof_core.Error × naming.Renamer) (renamed : Nnf) (count : Usize),
      NnfScoped signature scope formula → PredsBelow self.next.val (decodeNnf formula) →
      naming.Renamer.rename self formula limits = ok result → result.1 = .Ok (renamed, count) →
      RenamePost signature scope self.bodies.val self.next.val self.threshold formula renamed result.2 := by
  intro formula
  induction formula with
  | Literal literal =>
    intro self result renamed count valid below success completed
    unfold naming.Renamer.rename at success
    dsimp only at success
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Err error => residual_absurd
    | Ok _ =>
      step_ok
      obtain ⟨⟨answer1, work2⟩, _, success⟩ := bind_eq_ok success
      cases answer1 with
      | Err error => residual_absurd
      | Ok _ =>
        step_ok
        obtain ⟨⟨answer2, work3⟩, copied, success⟩ := bind_eq_ok success
        cases answer2 with
        | Err error => residual_absurd
        | Ok value =>
          step_ok
          have post := spec_eq_ok (copy_literal_spec literal valid limits work2) copied
          have same : value = literal := by simpa [CopyPost] using post.2
          rw [← ok_eq_ok success] at completed ⊢
          simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at completed
          obtain ⟨rfl, rfl⟩ := completed
          rw [same]
          exact post_copy valid rfl rfl rfl below
  | True | False =>
    intro self result renamed count valid below success completed
    unfold naming.Renamer.rename at success
    dsimp only at success
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Err error => residual_absurd
    | Ok _ =>
      step_ok
      obtain ⟨⟨answer1, work2⟩, _, success⟩ := bind_eq_ok success
      cases answer1 with
      | Err error => residual_absurd
      | Ok _ =>
        step_ok
        rw [← ok_eq_ok success] at completed ⊢
        simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at completed
        obtain ⟨rfl, rfl⟩ := completed
        exact post_copy valid rfl rfl rfl below
  | And left right ihl ihr =>
    intro self result renamed count valid below success completed
    unfold naming.Renamer.rename at success
    dsimp only at success
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Err error => residual_absurd
    | Ok _ =>
      step_ok
      obtain ⟨⟨answer1, work2⟩, _, success⟩ := bind_eq_ok success
      cases answer1 with
      | Err error => residual_absurd
      | Ok _ =>
        step_ok
        obtain ⟨⟨answerLeft, middle⟩, renamedLeft, success⟩ := bind_eq_ok success
        cases answerLeft with
        | Err error => residual_absurd
        | Ok pairLeft =>
          obtain ⟨left', countLeft⟩ := pairLeft
          step_ok
          have postLeft := ihl { self with work := work2 } _ left' countLeft valid.1 below.1 renamedLeft rfl
          obtain ⟨⟨answerRight, after⟩, renamedRight, success⟩ := bind_eq_ok success
          cases answerRight with
          | Err error => residual_absurd
          | Ok pairRight =>
            obtain ⟨right', countRight⟩ := pairRight
            step_ok
            have middleNext : self.next.val ≤ middle.next.val := by
              obtain ⟨_, _, newLeft, _⟩ := postLeft
              dsimp only at newLeft
              omega
            have postRight := ihr middle _ right' countRight valid.2
              (predsBelow_mono middleNext _ below.2) renamedRight rfl
            obtain ⟨sum, _, success⟩ := bind_eq_ok success
            rw [← ok_eq_ok success] at completed ⊢
            simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at completed
            obtain ⟨rfl, rfl⟩ := completed
            exact post_and postLeft postRight below.2
  | Or left right ihl ihr =>
    intro self result renamed count valid below success completed
    unfold naming.Renamer.rename at success
    dsimp only at success
    obtain ⟨⟨answer, work1⟩, _, success⟩ := bind_eq_ok success
    cases answer with
    | Err error => residual_absurd
    | Ok _ =>
      step_ok
      obtain ⟨⟨answer1, work2⟩, _, success⟩ := bind_eq_ok success
      cases answer1 with
      | Err error => residual_absurd
      | Ok _ =>
        step_ok
        obtain ⟨⟨answerLeft, middle⟩, renamedLeft, success⟩ := bind_eq_ok success
        cases answerLeft with
        | Err error => residual_absurd
        | Ok pairLeft =>
          obtain ⟨left', countLeft⟩ := pairLeft
          step_ok
          have postLeft := ihl { self with work := work2 } _ left' countLeft valid.1 below.1 renamedLeft rfl
          obtain ⟨⟨answerRight, after⟩, renamedRight, success⟩ := bind_eq_ok success
          cases answerRight with
          | Err error => residual_absurd
          | Ok pairRight =>
            obtain ⟨right', countRight⟩ := pairRight
            step_ok
            have middleNext : self.next.val ≤ middle.next.val := by
              obtain ⟨_, _, newLeft, _⟩ := postLeft
              dsimp only at newLeft
              omega
            have postRight := ihr middle _ right' countRight valid.2
              (predsBelow_mono middleNext _ below.2) renamedRight rfl
            have scopedLeft : NnfScoped signature scope left' := postLeft.choose_spec.2.2.2.1
            have scopedRight : NnfScoped signature scope right' := postRight.choose_spec.2.2.2.1
            -- The four tests of the naming rule; three of them leave the disjunction as it is.
            split at success
            · split at success
              · obtain ⟨product, _, success⟩ := bind_eq_ok success
                split at success
                · split at success
                  · -- The left side is named.
                    obtain ⟨⟨answerName, final⟩, named, success⟩ := bind_eq_ok success
                    cases answerName with
                    | Err error => residual_absurd
                    | Ok atom =>
                      step_ok
                      obtain ⟨vars, nextFinal, thresholdFinal, ⟨guard, bodiesFinal, guardDecoded, guardScoped⟩,
                        atomDecoded, atomScoped, exact⟩ := name_spec after left' scopedLeft limits _ named atom rfl
                      rw [← ok_eq_ok success] at completed ⊢
                      simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at completed
                      obtain ⟨rfl, rfl⟩ := completed
                      exact post_named postLeft postRight below.2 true atom vars nextFinal thresholdFinal guard
                        bodiesFinal (by simpa using guardDecoded) guardScoped atomDecoded atomScoped
                        (by simpa using exact)
                  · -- The right side is named.
                    obtain ⟨⟨answerName, final⟩, named, success⟩ := bind_eq_ok success
                    cases answerName with
                    | Err error => residual_absurd
                    | Ok atom =>
                      step_ok
                      obtain ⟨vars, nextFinal, thresholdFinal, ⟨guard, bodiesFinal, guardDecoded, guardScoped⟩,
                        atomDecoded, atomScoped, exact⟩ := name_spec after right' scopedRight limits _ named atom rfl
                      rw [← ok_eq_ok success] at completed ⊢
                      simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at completed
                      obtain ⟨rfl, rfl⟩ := completed
                      exact post_named postLeft postRight below.2 false atom vars nextFinal thresholdFinal guard
                        bodiesFinal (by simpa using guardDecoded) guardScoped atomDecoded atomScoped
                        (by simpa using exact)
                · rw [← ok_eq_ok success] at completed ⊢
                  simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at completed
                  obtain ⟨rfl, rfl⟩ := completed
                  exact post_or postLeft postRight below.2
              · obtain ⟨product, _, success⟩ := bind_eq_ok success
                rw [← ok_eq_ok success] at completed ⊢
                simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at completed
                obtain ⟨rfl, rfl⟩ := completed
                exact post_or postLeft postRight below.2
            · obtain ⟨product, _, success⟩ := bind_eq_ok success
              rw [← ok_eq_ok success] at completed ⊢
              simp only [core.result.Result.Ok.injEq, Prod.mk.injEq] at completed
              obtain ⟨rfl, rfl⟩ := completed
              exact post_or postLeft postRight below.2

end FangNaming
