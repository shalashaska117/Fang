/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed endpoint types for depth, cited-premise replay and named documents. -/
import NamedDocument
import NamedCited
import NamedCitedDepth

namespace Fang.TptpCandidate.Roles.Bundle.V3.Depth
example (limit : Nat) : Bytes.decodeBytesLimitedD limit 64 = Bytes.decodeBytesLimited limit :=
  Bytes.decodeBytesLimitedD_accepted limit

example (limit maxDepth : Nat) :
    frameBundleHashed limit maxDepth = frameBundle limit maxDepth V2.gated :=
  frameBundleHashed_eq limit maxDepth

example (limit : Nat) : frameBundleHashed limit 64 = V3.frameBundleHashed limit :=
  frameBundleHashed_accepted limit

example {frame : Frame} (sound : FrameSound frame)
    {files maximumBytes index cited proof limits threshold maximumPredicates maximumLiterals item}
    (accepted : Named.acceptsGoalCited frame files maximumBytes index cited proof limits threshold maximumPredicates
      maximumLiterals = .ok item) :
    GoalEntailed frame files maximumBytes bundleFuel item :=
  Named.acceptsGoalCited_entails sound accepted

example {frame : Frame} (sound : FrameSound frame)
    {files maximumBytes cited proof limits threshold maximumPredicates maximumLiterals}
    (accepted : Named.acceptsInputsCited frame files maximumBytes cited proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ByteUnsatisfiable frame files maximumBytes bundleFuel :=
  Named.acceptsInputsCited_unsat sound accepted

example {frame : Frame} (sound : FrameSound frame)
    {files maximumBytes bundle items limits threshold maximumPredicates maximumLiterals}
    (expanded : Expanded frame files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index cited proof,
      Named.acceptsGoalCited frame files maximumBytes index cited proof limits threshold maximumPredicates
        maximumLiterals = .ok pair.1) :
    ByteTheorem frame files maximumBytes bundleFuel :=
  Named.acceptsGoalsCited_theorem sound expanded nonempty accepted
end Fang.TptpCandidate.Roles.Bundle.V3.Depth

namespace Fang.QuantifiedEqualityTstp.NamedExport
example {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file text}
    (success : exportDocument limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals file =
      .ok text) :
    ¬ Fang.TptpCandidate.FullFof.CnfBoolean.BytesSatisfiable bytes maximumBytes :=
  exportDocument_original_unsat success
end Fang.QuantifiedEqualityTstp.NamedExport

#print axioms Fang.QuantifiedEqualityTstp.NamedExport.attach_spec
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.build_accepts
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.build_check
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.build_group_sap
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.build_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.build_row_checked
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.build_rows
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.build_witness
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.check_spec
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.document_group
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.document_group_sap
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.document_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.document_spec
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.exportDocument_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.exportDocument_spec
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.final_row_empty
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.group_models
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.group_sap
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.namedModel_models
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.originals_decoded
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.readInput_originals
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.row_local
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.named_models
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.prepareNamed_models
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.prepareNamed_original
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.replayNamedFrom_models
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.byteTheorem_of_entailed
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.contains_insert_cons
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.distinct_below
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.distinctItems_models
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.entries_closed
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.entries_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.formulaRecord_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.formulaRecord_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.formulaRecordFast_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.formulaRecordHashed_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.frameBundle_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.frameBundle_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.frameBundleHashed_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.frameBundleHashed_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.frameBundleHashed_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.frameFileHashed_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.goal_entailed_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.goal_holds_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.goal_holds_of_refuted_lifted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.goal_item_entailed
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.inputs_fail_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.inputs_fail_of_refuted_lifted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.acceptsGoal_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.acceptsGoalCited_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.acceptsGoals_theorem
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.acceptsGoalsCited_theorem
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.acceptsInputs_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.acceptsInputsCited_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.prepareGoal_check_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.prepareGoal_witness
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.prepareGoalCited_check_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.prepareGoalCited_witness
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.prepareInputs_check_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.prepareInputsCited_check_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.Named.prepareInputsCited_witness
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.objectIds_nodup
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.objects_covered
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.statements_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.statements_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.statementsHashed_eq
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.task_below
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Depth.unsatisfiable_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsGoalCited_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsGoalCitedLimited_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsGoalsCited_theorem
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsGoalsCitedLimited_theorem
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsInputsCited_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsInputsCitedLimited_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.citedEntries_every
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.citedRead_every
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.prepareGoalCited_check_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.prepareGoalCited_witness
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.prepareInputsCited_check_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.prepareInputsCited_witness
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationCD_accepted
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationCD_eq
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationD_accepted
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationD_closed
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationD_goal_fof
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationD_sound
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationD_witness
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationSeenCD_accepted
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationSeenCD_eq
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsHashedD_eq
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsUpToD_accepted_at
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsUpToD_closed
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsUpToD_goals_fof
#print axioms Fang.TptpCandidate.Roles.Bytes.declarationsUpToD_sound
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeBytesLimitedD_accepted
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeBytesLimitedD_eq
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeBytesUpToD_accepted
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeUpToD_closed
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeUpToD_goals_fof
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeUpToD_grammar
#print axioms Fang.TptpCandidate.Roles.Bytes.decodeUpToD_has_tokens
