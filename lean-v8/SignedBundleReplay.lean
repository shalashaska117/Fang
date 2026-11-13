/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed role tasks over sealed include bundles through the accepted signed replay and the version-8 `checkProblem`. The generated distinct-object disequalities enter each task as positive CNF items. -/
import BundleItems
import BundleRead
import SignedEnvelope

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Bundle
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

/-! The replay theorem with an explicit function-range premise in place of row provenance. -/

theorem replayTask_check_unsat_below {input task limits maximumPredicates maximumLiterals prepared}
    (below : FangQuantifiedPipeline.ProblemBelow input.functions.length (retainedClauses task))
    (success : Signed.replayTask input task limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ TaskSatisfiable input task := by
  obtain ⟨encoded, declarations, slice, transformed, blocks, ordinary, inputRun, declarationsRun,
    sliceValues, skolemRun, steps, layout, converted, _, _⟩ := Signed.replayTask_witness success
  rintro ⟨D, nonempty, model, holds⟩
  let : Nonempty D := nonempty
  obtain ⟨valid, _, slot, _, functions, _⟩ := Integration.transport_tables inputRun
  obtain ⟨retainedHold, signedHold⟩ := taskModels_parts holds
  have signedDeclarations : FangQuantifiedPipeline.SignedDeclarationsHold
      (FullFof.reserve input.predicates.length model) slice.val := by
    rw [sliceValues]
    exact (signed_hold (encodeSigned_related declarationsRun) _).mpr signedHold
  have reservedHolds :
      (retainedClauses task).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model) ∧
      FangQuantifiedPipeline.SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model) slice.val := by
    rw [slot, ← Integration.reserve_interpretation]
    exact ⟨retainedHold, signedDeclarations⟩
  have count : encoded.signature.functions.val.length = input.functions.length := by
    simpa only [List.length_map, Signed.tables] using congrArg List.length functions
  have range : FangQuantifiedPipeline.ProblemBelow encoded.signature.functions.val.length
      (retainedClauses task) := by
    rw [count]
    exact below
  obtain ⟨extended, preserved, grouped⟩ := FangQuantifiedPipeline.skolem_actual_problem_models skolemRun
    (retainedClauses task) range blocks steps
    (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model)
  have parts := (FangQuantifiedPipeline.models_append extended _ _).mp (grouped.mpr reservedHolds)
  have mixedModel : ordinary.Models extended := by
    apply (Fang.QuantifiedCertificate.mixedLayout_models layout extended).mpr
    rw [Signed.retained_taskDeclarations]
    exact parts
  have equalityModel := (FangQuantifiedEquality.actualProblem_models model extended
    encoded.reservation encoded.signature.functions.val.length valid preserved converted).mp mixedModel
  exact Fang.Equality.Ordered.check_unsat prepared.problem certificate accepted
    ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation model extended, equalityModel⟩

theorem retainedClauses_append : ∀ (left right : List SignedNumeric),
    retainedClauses (left ++ right) = retainedClauses left ++ retainedClauses right
  | [], _ => rfl
  | .cnf clause :: rest, right => by
    simp only [List.cons_append, retainedClauses, retainedClauses_append rest right]
  | .fof positive formula :: rest, right => by
    simp only [List.cons_append, retainedClauses, retainedClauses_append rest right]

/-- The generated disequalities mention only nullary IDs of the complete function table. -/
theorem distinct_below {files : List (Coverage.Key × List UInt8)} {maximum : Nat} {bundle : RoleBundle}
    (framed : frameBundle files maximum = .ok bundle) {items : List Coverage.Item} {input : SignedInput}
    (read : readSigned (entriesOf bundle items) = some input) :
    FangQuantifiedPipeline.ProblemBelow input.functions.length (retainedClauses (distinctItems input bundle items)) := by
  have covered := framed_objects_covered framed items (read_tables read)
  have bound : ∀ id ∈ objectIds input bundle items, id < input.functions.length := by
    intro id member
    simp only [objectIds, List.mem_map] at member
    obtain ⟨label, labelMember, rfl⟩ := member
    exact Arity.id_bound (covered label labelMember)
  intro clause member literal literalMember term termMember
  have present := mem_retainedClauses member
  simp only [distinctItems, Coverage.distinctAxioms, List.map_map, List.mem_map, Function.comp_def] at present
  obtain ⟨⟨left, right⟩, pairMember, shape⟩ := present
  simp only [Coverage.disequality, positive, SignedNumeric.cnf.injEq] at shape
  subst shape
  obtain ⟨leftMember, rightMember, _⟩ := Coverage.pairs_mem pairMember
  simp only [List.mem_singleton] at literalMember
  subst literalMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at termMember
  rcases termMember with rfl | rfl
  · simp only [Fang.QuantifiedFOF.Skolem.TermBelow]
    exact ⟨bound left leftMember, by simp⟩
  · simp only [Fang.QuantifiedFOF.Skolem.TermBelow]
    exact ⟨bound right rightMember, by simp⟩

theorem task_below {files : List (Coverage.Key × List UInt8)} {maximum : Nat} {bundle : RoleBundle}
    (framed : frameBundle files maximum = .ok bundle) {items : List Coverage.Item} {input : SignedInput}
    (read : readSigned (entriesOf bundle items) = some input) {task : List SignedNumeric}
    (fromRows : FromRows input task) :
    FangQuantifiedPipeline.ProblemBelow input.functions.length
      (retainedClauses (task ++ distinctItems input bundle items)) := by
  rw [retainedClauses_append]
  intro clause member
  rcases List.mem_append.mp member with original | generated
  · exact retained_below read fromRows clause original
  · exact distinct_below framed read clause generated

/-! Bundle entries. -/

inductive BundleError where
  | read : BundleReadError → BundleError
  | noGoal
  | cnfGoal
  | goalsPresent
  | replay : Signed.SignedError → BundleError

structure BundleGoalPrepared where
  item : Coverage.Item
  replay : Signed.SignedPrepared

/-- The task for the conjecture with this index among all selected conjectures, in expansion order; `item` is its bundle identity. -/
def prepareBundleGoal (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleError BundleGoalPrepared := do
  let read ← (readBundle files maximumBytes).mapError .read
  let some (before, goal, after) := (Signed.goalSplits read.input)[index]? | .error .noGoal
  let some (item, _) := (goalItems read.bundle read.items)[index]? | .error .noGoal
  let some task := goalTask before goal after | .error .cnfGoal
  let replay ← (Signed.replayTask read.input (task ++ distinctItems read.input read.bundle read.items)
    limits maximumPredicates maximumLiterals).mapError .replay
  pure ⟨item, replay⟩

/-- The satisfiability task, only when no conjecture is selected. -/
def prepareBundleInputs (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleError Signed.SignedPrepared := do
  let read ← (readBundle files maximumBytes).mapError .read
  if (goalItems read.bundle read.items).isEmpty then
    (Signed.replayTask read.input (inputsTask read.input ++ distinctItems read.input read.bundle read.items)
      limits maximumPredicates maximumLiterals).mapError .replay
  else .error .goalsPresent

theorem prepareBundleGoal_witness {files maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareBundleGoal files maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared) :
    ∃ read before goal after entry task, readBundle files maximumBytes = .ok read ∧
      (Signed.goalSplits read.input)[index]? = some (before, goal, after) ∧
      (goalItems read.bundle read.items)[index]? = some (prepared.item, entry) ∧
      goalTask before goal after = some task ∧
      Signed.replayTask read.input (task ++ distinctItems read.input read.bundle read.items)
        limits maximumPredicates maximumLiterals = .ok prepared.replay := by
  obtain ⟨read, readRun, success⟩ := bind_success success
  cases selected : (Signed.goalSplits read.input)[index]? with
  | none => simp [selected] at success
  | some split =>
    obtain ⟨before, goal, after⟩ := split
    cases identified : (goalItems read.bundle read.items)[index]? with
    | none => simp [selected, identified] at success
    | some pair =>
      obtain ⟨item, entry⟩ := pair
      cases built : goalTask before goal after with
      | none => simp [selected, identified, built] at success
      | some task =>
        simp only [selected, identified, built] at success
        obtain ⟨replay, replayRun, success⟩ := bind_success success
        cases Except.ok.inj success
        exact ⟨read, before, goal, after, entry, task, mapError_success readRun, selected, identified, built,
          mapError_success replayRun⟩

/-- Checker acceptance on one goal task proves that goal, identified by its bundle item, from the selected premises under distinct-object separation. -/
theorem prepareBundleGoal_check_entails {files maximumBytes index limits maximumPredicates maximumLiterals prepared}
    (success : prepareBundleGoal files maximumBytes index limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.replay.problem certificate = .ok ()) :
    BundleGoalEntailed files maximumBytes bundleFuel prepared.item := by
  obtain ⟨read, before, goal, after, entry, task, readRun, selected, identified, built, replayRun⟩ :=
    prepareBundleGoal_witness success
  obtain ⟨expanded, signed⟩ := readBundle_witness readRun
  have split := (Signed.goalSplits_member (List.mem_of_getElem? selected)).1
  have unsat := replayTask_check_unsat_below
    (task_below expanded.1 signed (goalTask_fromRows split built)) replayRun certificate accepted
  exact goal_item_entailed expanded signed selected identified built unsat

/-- The Unsatisfiable statement over a bundle: it frames, is well shaped and expands, no conjecture is selected, and the positive inputs have no model that keeps distinct objects apart. Unlike `¬ ByteBundleInputsSatisfiable`, it is false for a bundle with a selected conjecture. -/
def ByteBundleUnsatisfiable (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, Expanded files maximum fuel bundle items ∧ goalItems bundle items = [] ∧
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.Framer.NamedSeparated model (objectsOf bundle items) →
      ¬ Roles.AllHold (Bytes.sentence (D := D)) (Roles.positiveInputs (Bytes.source (entriesOf bundle items))) model

theorem unsatisfiable_not_satisfiable {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    (unsat : ByteBundleUnsatisfiable files maximum fuel) : ¬ ByteBundleInputsSatisfiable files maximum fuel := by
  rintro ⟨other, others, otherExpanded, _, D, inhabited, model, separated, holds⟩
  obtain ⟨bundle, items, expanded, _, refuted⟩ := unsat
  obtain ⟨rfl, rfl⟩ := expanded_unique expanded otherExpanded
  exact refuted D inhabited model separated holds

/-- Checker acceptance on the no-goal task proves the Unsatisfiable statement; the entry refuses a bundle with a selected conjecture. -/
theorem prepareBundleInputs_check_unsat {files maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepareBundleInputs files maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ByteBundleUnsatisfiable files maximumBytes bundleFuel := by
  obtain ⟨read, readRun, success⟩ := bind_success success
  obtain ⟨expanded, signed⟩ := readBundle_witness (mapError_success readRun)
  split at success
  · rename_i empty
    have noGoals := List.isEmpty_iff.mp empty
    have unsat := inputs_unsat_of_refuted expanded signed (replayTask_check_unsat_below
      (task_below expanded.1 signed (inputsTask_fromRows read.input)) (mapError_success success) certificate accepted)
    refine ⟨read.bundle, read.items, expanded, noGoals, ?_⟩
    intro D inhabited model separated holds
    exact unsat ⟨read.bundle, read.items, expanded, noGoals, D, inhabited, model, separated, holds⟩
  · cases success

/-! Version-8 acceptance over bundles. -/

inductive BundleAcceptError where
  | replay : BundleError → BundleAcceptError
  | certificate : FullFof.Integration.CertificateError → BundleAcceptError

/-- Accepts the certificate for one goal index and returns that goal's bundle item. -/
def acceptsBundleGoal (files : List (Coverage.Key × List UInt8)) (maximumBytes index : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleAcceptError Coverage.Item := do
  let prepared ← (prepareBundleGoal files maximumBytes index limits maximumPredicates maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.replay.problem prepared.replay.functionArities
    prepared.replay.predicateArities proof).mapError .certificate
  pure prepared.item

def acceptsBundleInputs (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Except BundleAcceptError Unit := do
  let prepared ← (prepareBundleInputs files maximumBytes limits maximumPredicates maximumLiterals).mapError .replay
  (FullFof.Integration.checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

theorem acceptsBundleGoal_entails {files maximumBytes index proof limits maximumPredicates maximumLiterals item}
    (accepted : acceptsBundleGoal files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok item) :
    BundleGoalEntailed files maximumBytes bundleFuel item := by
  obtain ⟨prepared, run, rest⟩ := bind_success accepted
  obtain ⟨_, checked, finished⟩ := bind_success rest
  cases Except.ok.inj finished
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareBundleGoal_check_entails (mapError_success run) parsed refuted

theorem acceptsBundleInputs_unsat {files maximumBytes proof limits maximumPredicates maximumLiterals}
    (accepted : acceptsBundleInputs files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ByteBundleUnsatisfiable files maximumBytes bundleFuel := by
  obtain ⟨prepared, run, checked⟩ := bind_success accepted
  obtain ⟨parsed, _, _, _, refuted⟩ := FullFof.Integration.checkProblem_success (mapError_success checked)
  exact prepareBundleInputs_check_unsat (mapError_success run) parsed refuted

theorem goalItems_entry {bundle : RoleBundle} {items : List Coverage.Item} {item : Coverage.Item}
    {entry : Bytes.Entry} (member : (item, entry) ∈ goalItems bundle items) :
    roleStatementAt bundle item = some (.formula entry) := by
  simp only [goalItems, List.mem_filter, List.mem_filterMap] at member
  obtain ⟨⟨other, _, found⟩, _⟩ := member
  cases statementAt : roleStatementAt bundle other with
  | none => simp [statementAt] at found
  | some statement =>
    cases statement with
    | directive parts selection => simp [statementAt] at found
    | formula value =>
      simp only [statementAt, Option.some.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, rfl⟩ := found
      exact statementAt

/-- Theorem endpoint over a bundle: at least one selected conjecture, and an accepted version-8 certificate for every goal item. -/
theorem acceptsBundleGoals_theorem {files maximumBytes bundle items limits maximumPredicates maximumLiterals}
    (expanded : Expanded files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index proof,
      acceptsBundleGoal files maximumBytes index proof limits maximumPredicates maximumLiterals = .ok pair.1) :
    ByteBundleTheorem files maximumBytes bundleFuel := by
  refine ⟨bundle, items, expanded, nonempty, ?_⟩
  intro ⟨item, value⟩ member D inhabited model separated premisesHold
  obtain ⟨index, proof, run⟩ := accepted (item, value) member
  obtain ⟨other, others, entry, otherExpanded, otherMember, entails⟩ := acceptsBundleGoal_entails run
  obtain ⟨rfl, rfl⟩ := expanded_unique expanded otherExpanded
  have first := goalItems_entry otherMember
  have second := goalItems_entry member
  rw [first] at second
  simp only [Option.some.injEq, RoleStatement.formula.injEq] at second
  rw [← second]
  exact entails D inhabited model separated premisesHold

#print axioms Fang.TptpCandidate.Roles.Bundle.replayTask_check_unsat_below
#print axioms Fang.TptpCandidate.Roles.Bundle.retainedClauses_append
#print axioms Fang.TptpCandidate.Roles.Bundle.distinct_below
#print axioms Fang.TptpCandidate.Roles.Bundle.task_below
#print axioms Fang.TptpCandidate.Roles.Bundle.prepareBundleGoal_witness
#print axioms Fang.TptpCandidate.Roles.Bundle.prepareBundleGoal_check_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.unsatisfiable_not_satisfiable
#print axioms Fang.TptpCandidate.Roles.Bundle.prepareBundleInputs_check_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.acceptsBundleGoal_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.acceptsBundleInputs_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.goalItems_entry
#print axioms Fang.TptpCandidate.Roles.Bundle.acceptsBundleGoals_theorem

end Fang.TptpCandidate.Roles.Bundle
