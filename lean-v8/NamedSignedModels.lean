/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Model preservation for named signed tasks and their TSTP groups. -/
import NamedSigned
import NamedModels
import GoalDocument

namespace Fang.TptpCandidate.Roles.Signed
open FullFof Numeric
open FangQuantifiedEqualityReplay (bind_success mapError_success)

theorem replayNamedTask_models_below {input task limits threshold maximumPredicates maximumLiterals prepared}
    (below : FangQuantifiedPipeline.ProblemBelow input.functions.length (retainedClauses task))
    (success : replayNamedTask input task limits threshold maximumPredicates maximumLiterals = .ok prepared)
    (satisfiable : TaskSatisfiable input task) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  unfold replayNamedTask at success
  obtain ⟨encoded, inputRun, success⟩ := bind_success success
  obtain ⟨declarations, declarationsRun, success⟩ := bind_success success
  obtain ⟨slice, sliceRun, success⟩ := bind_success success
  obtain ⟨transformed, skolemRun, success⟩ := bind_success success
  obtain ⟨first, firstRun, success⟩ := bind_success success
  obtain ⟨named, namedRun, success⟩ := bind_success success
  obtain ⟨ordinary, assemblyRun, success⟩ := bind_success success
  obtain ⟨finished, finishRun, success⟩ := bind_success success
  cases Except.ok.inj success
  obtain ⟨D, nonempty, model, holds⟩ := satisfiable
  let : Nonempty D := nonempty
  obtain ⟨valid, _, slot, _, functions, _⟩ := Integration.transport_tables (mapError_success inputRun)
  obtain ⟨retainedHold, signedHold⟩ := taskModels_parts holds
  have signedDeclarations : FangQuantifiedPipeline.SignedDeclarationsHold
      (FullFof.reserve input.predicates.length model) slice.val := by
    rw [FangOriginalInput.checkedSlice_values (mapError_success sliceRun)]
    exact (signed_hold (encodeSigned_related (mapError_success declarationsRun)) _).mpr signedHold
  have reservedHolds :
      (retainedClauses task).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model) ∧
      FangQuantifiedPipeline.SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model) slice.val := by
    rw [slot, ← Integration.reserve_interpretation]
    exact ⟨retainedHold, signedDeclarations⟩
  have count : encoded.signature.functions.val.length = input.functions.length := by
    simpa only [List.length_map, tables] using congrArg List.length functions
  have bounded : FangQuantifiedPipeline.ProblemBelow encoded.signature.functions.val.length
      (retainedClauses task) := by
    rw [count]
    exact below
  have skolemSuccess := FangOriginalReplay.observe_success (mapError_success skolemRun)
  obtain ⟨skolemized, preserved, meaning⟩ := FangSkolemCore.skolemize_problem_independent_meaning
    skolemSuccess (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val model)
  have retainedModels : (Fang.QuantifiedCertificate.retained (taskDeclarations task)).Models skolemized := by
    rw [retained_taskDeclarations]
    exact (FangQuantifiedPipeline.problem_preserved preserved _ bounded).mpr reservedHolds.1
  obtain ⟨result, models⟩ := Integration.Named.named_models valid (mapError_success firstRun) (mapError_success namedRun)
    (mapError_success assemblyRun) (mapError_success finishRun) model skolemized preserved
    (fun formula member =>
      ⟨⟨_, FangQuantifiedPipeline.skolemize_problem_scoped skolemSuccess formula member⟩,
        (FangSkolemCore.skolemize_problem_output skolemSuccess formula member).1,
        fun valuation => (meaning valuation).mp
          (fun declaration present => reservedHolds.2 declaration present valuation) formula member⟩)
    retainedModels
  exact ⟨D, nonempty, result, models⟩

theorem prepareGoalNamed_models {limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (countermodel : GoalDocument.GoalCountermodel bytes maximumBytes prepared.goal) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.replay.problem := by
  obtain ⟨values, input, before, goal, after, task, decoded, read, selected, built, replayRun, goalSame⟩ :=
    prepareGoalNamed_witness success
  have split := (goalSplits_member (List.mem_of_getElem? selected)).1
  obtain ⟨other, parsed, D, inhabited, model, premisesHold, fails⟩ := countermodel
  have sources := Bytes.byteParsed_source_unique parsed (Bytes.decodeUpTo_grammar decoded)
  rw [sources] at premisesHold
  rw [goalSame] at fails
  have satisfiable := (goalTask_satisfiable_iff read (Bytes.decodeUpTo_closed decoded) split built).mpr
    ⟨D, inhabited, model, premisesHold, fails⟩
  exact replayNamedTask_models_below (retained_below read (goalTask_fromRows split built)) replayRun satisfiable

end Fang.TptpCandidate.Roles.Signed
