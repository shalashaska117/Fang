import NamedCitedDocumentTrace
import CitedSourceRows

namespace Fang.TptpCandidate.CitedDocument
open FullFof Roles.Numeric Roles.Bundle Roles.Bundle.V3 Roles.Bundle.V3.Depth
open Fang.QuantifiedEqualityTstp

def GoalCountermodel (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (cited : List Coverage.Item) (item : Coverage.Item) : Prop :=
  ∃ (read : BundleRead) (entry : Roles.Bytes.Entry),
    readBundle frame files maximumBytes = .ok read ∧
    roleStatementAt read.bundle item = some (.formula entry) ∧
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf read.bundle (keptItems read.items cited (some item))) ∧
      Roles.AllHold (Roles.Bytes.sentence (D := D))
        (Roles.premises (Roles.Bytes.source (entriesOf read.bundle (keptItems read.items cited (some item))))) model ∧
      ¬ Roles.Bytes.sentence model (entryDeclaration entry).original

theorem prepare_goal_models {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {files maximumBytes index cited limits threshold maximumPredicates maximumLiterals prepared}
    (success : Named.prepareGoalCited frame files maximumBytes index cited limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (countermodel : GoalCountermodel frame files maximumBytes cited prepared.item) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.replay.problem := by
  obtain ⟨read, entry, input, position, before, goal, after, keptEntry, task, readRun, identified, readKept,
    located, selected, built, replayRun⟩ := Named.prepareGoalCited_witness success
  obtain ⟨expanded, _, _⟩ := readBundle_witness readRun
  have sound := frameSound expanded.1
  have split := (Roles.Signed.goalSplits_member (List.mem_of_getElem? selected)).1
  have declared : goal.declaration = entryDeclaration keptEntry := by
    have chosen : ((splits input.rows).filter (fun split => decide (split.2.1.role = .conjecture)))[position]? =
        some (before, goal, after) := selected
    have mapped := congrArg (fun list => list[position]?) (goal_rows_items readKept)
    simp only [List.getElem?_map, chosen, located, Option.map_some, Option.some.injEq] at mapped
    exact mapped
  obtain ⟨other, original, otherRun, originalAt, D, inhabited, model, separated, premisesHold, fails⟩ := countermodel
  have sameRead : other = read := Except.ok.inj (otherRun.symm.trans readRun)
  subst other
  have keptAt := V2.goalItems_entry (List.mem_of_getElem? located)
  rw [keptAt] at originalAt
  have sameEntry : original = keptEntry := by simpa using originalAt.symm
  subst original
  let _ : Nonempty D := inhabited
  have satisfiable : TaskSatisfiable input (task ++ V2.distinctItems input read.bundle (keptItems read.items cited (some prepared.item))) := by
    refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
    rw [taskModels_append]
    refine ⟨(goalTask_models readKept (entries_closed sound _) split built (model_toNumeric model _ _)).mpr ?_,
      distinctItems_models sound readKept model separated⟩
    refine ⟨premisesHold, (Roles.negative_holds _ _).mpr ?_⟩
    simpa only [declared] using fails
  exact Roles.Signed.replayNamedTask_models_below
    (task_below sound readKept (goalTask_fromRows split built)) replayRun satisfiable

def InputsModel (frame : Frame) (files : List (Coverage.Key × List UInt8)) (maximumBytes : Nat)
    (cited : List Coverage.Item) : Prop :=
  ∃ (read : BundleRead), readBundle frame files maximumBytes = .ok read ∧
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.FramerV2.NamedSeparated model (V2.objectsOf read.bundle (keptItems read.items cited none)) ∧
      Roles.AllHold (Roles.Bytes.sentence (D := D))
        (Roles.positiveInputs (Roles.Bytes.source (entriesOf read.bundle (keptItems read.items cited none)))) model

theorem prepare_inputs_models {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {files maximumBytes cited limits threshold maximumPredicates maximumLiterals prepared}
    (success : Named.prepareInputsCited frame files maximumBytes cited limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (satisfiable : InputsModel frame files maximumBytes cited) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  obtain ⟨read, input, readRun, _, readKept, replayRun⟩ := Named.prepareInputsCited_witness success
  obtain ⟨expanded, _, _⟩ := readBundle_witness readRun
  have sound := frameSound expanded.1
  obtain ⟨other, otherRun, D, inhabited, model, separated, holds⟩ := satisfiable
  have sameRead : other = read := Except.ok.inj (otherRun.symm.trans readRun)
  subst other
  let _ : Nonempty D := inhabited
  have taskModels : TaskSatisfiable input (inputsTask input ++ V2.distinctItems input read.bundle (keptItems read.items cited none)) := by
    refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
    rw [taskModels_append]
    exact ⟨(inputsTask_models readKept (entries_closed sound _) (model_toNumeric model _ _)).mpr holds,
      distinctItems_models sound readKept model separated⟩
  exact Roles.Signed.replayNamedTask_models_below
    (task_below sound readKept (inputsTask_fromRows input)) replayRun taskModels

def objectStem (replay : Roles.Signed.SignedPrepared) : String :=
  Expanded.freshPrefix (Naming.originalNames replay.input.functions replay.input.predicates) "obj" "o"

def printableFunctions (replay : Roles.Signed.SignedPrepared) : List (String × Nat) :=
  Fang.QuantifiedEqualityTstp.Expanded.Bundle.renameObjects (objectStem replay) replay.input.functions

def outputNames (replay : Roles.Signed.SignedPrepared) : Body.Names :=
  NamedExport.exportNames (printableFunctions replay) replay.input.predicates replay.functionArities replay.predicateArities

def attachNames (replay : Roles.Signed.SignedPrepared) (names : Body.Names) : Except String Body.Names :=
  NamedExport.check (printableFunctions replay) replay.input.predicates
    ⟨replay.problem, replay.functionArities, replay.predicateArities⟩ names

theorem attachNames_spec {replay proposed names} (success : attachNames replay proposed = .ok names) :
    NamedExport.Checked (printableFunctions replay) replay.input.predicates
      ⟨replay.problem, replay.functionArities, replay.predicateArities⟩ names :=
  NamedExport.check_spec success

theorem goal_group_sap {frame : Frame} (frameSound : Roles.Bundle.V3.Depth.FrameSound frame)
    {files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals output}
    (built : build frame files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals = .ok output)
    {proposed names} (named : attachNames output.prepared.replay proposed = .ok names)
    {formula} (formulaRun : Group.groupFormula names output.prepared.replay.problem = .ok formula)
    (countermodel : GoalCountermodel frame files maximumBytes cited output.prepared.item) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨preparedRun, _, wellFormed, _⟩ := build_witness built
  simp only [CitedDocument.wellFormed, GoalDocument.NamedDepth.GoalWellFormed, Bool.and_eq_true] at wellFormed
  obtain ⟨D, nonempty, model, holds⟩ := prepare_goal_models frameSound preparedRun countermodel
  exact ⟨D, nonempty, Expanded.namedModel names model,
    NamedExport.group_models (attachNames_spec named) wellFormed.1 formulaRun model holds⟩

#print axioms prepare_goal_models
#print axioms prepare_inputs_models
#print axioms attachNames_spec
#print axioms goal_group_sap
end Fang.TptpCandidate.CitedDocument
