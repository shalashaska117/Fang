import NamedSignedDepth
import NamedSignedModels
namespace Fang.TptpCandidate.Roles.Signed.DepthNamed
open FullFof Numeric
theorem prepareGoalNamed_models {limit maxDepth bytes maximumBytes index limits threshold maximumPredicates maximumLiterals prepared}
    (success : prepareGoalNamed limit maxDepth bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (countermodel : GoalDocument.GoalCountermodel bytes maximumBytes prepared.goal) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.replay.problem := by
  obtain ⟨values, input, before, goal, after, task, decoded, read, selected, built, replayRun, goalSame⟩ :=
    prepareGoalNamed_witness success
  have split := (goalSplits_member (List.mem_of_getElem? selected)).1
  obtain ⟨other, parsed, D, inhabited, model, premisesHold, fails⟩ := countermodel
  have sources := Bytes.byteParsed_source_unique parsed (Bytes.decodeUpToD_grammar decoded)
  rw [sources] at premisesHold
  rw [goalSame] at fails
  have satisfiable := (goalTask_satisfiable_iff read (Bytes.decodeUpToD_closed decoded) split built).mpr
    ⟨D, inhabited, model, premisesHold, fails⟩
  exact replayNamedTask_models_below (retained_below read (goalTask_fromRows split built)) replayRun satisfiable


end Fang.TptpCandidate.Roles.Signed.DepthNamed
