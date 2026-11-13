/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Explicit named document endpoints and a fixed theorem audit. -/
import NamedGoalDocument
import NamedBundleDocument
import SignedBundleNativeV6Core

namespace Fang.TptpCandidate.GoalDocument.Named
example {limit bytes maximumBytes index proof limits threshold maximumPredicates maximumLiterals output}
    (success : buildGoal limit bytes maximumBytes index proof limits threshold maximumPredicates maximumLiterals = .ok output) :
    ∃ values, Roles.Bytes.ByteParsed bytes maximumBytes values ∧ Roles.Bytes.Closed values ∧
      output.prepared.goal ∈ Roles.goals (Roles.Bytes.source values) ∧
      ∀ (D : Type) (_ : Nonempty D) (model : Fang.Source.Interpretation D),
        Roles.AllHold (Roles.Bytes.sentence (D := D)) (Roles.premises (Roles.Bytes.source values)) model →
          Roles.Bytes.sentence model output.prepared.goal.original := buildGoal_entails success
end Fang.TptpCandidate.GoalDocument.Named

namespace Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named
example {frame : Fang.TptpCandidate.FullFof.Coverage.FramerLimit.Frame}
    (frameSound : Fang.TptpCandidate.FullFof.Coverage.FramerLimit.FrameSound frame)
    {files maximumBytes proof limits threshold maximumPredicates maximumLiterals text}
    (success : exportBundleDocument frame files maximumBytes proof limits threshold maximumPredicates maximumLiterals = .ok text) :
    Fang.TptpCandidate.FullFof.Coverage.BundleLimit.BundleRefuted frame files maximumBytes
      Fang.TptpCandidate.FullFof.Coverage.BundleV8.bundleFuel := exportBundleDocument_refuted frameSound success
end Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named

#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.attachBundle_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.buildBundle_accepts
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.buildBundle_check
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.buildBundle_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.buildBundle_row_checked
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.buildBundle_rows
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.buildBundle_sources
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.buildBundle_witness
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.bundleDocumentOf_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.bundleDocument_group_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.bundleDocument_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.bundleDocument_rows_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.bundleDocument_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.bundle_group_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.exportBundleDocument_hashed_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.exportBundleDocument_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.exportBundleDocument_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.Named.prepareBundle_models
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.replayNamedFrom_original
#print axioms Fang.TptpCandidate.GoalDocument.Named.buildGoal_accepts
#print axioms Fang.TptpCandidate.GoalDocument.Named.buildGoal_check
#print axioms Fang.TptpCandidate.GoalDocument.Named.buildGoal_entails
#print axioms Fang.TptpCandidate.GoalDocument.Named.buildGoal_witness
#print axioms Fang.TptpCandidate.GoalDocument.Named.exportGoalDocument_spec
#print axioms Fang.TptpCandidate.GoalDocument.Named.goalCountermodel_negated
#print axioms Fang.TptpCandidate.GoalDocument.Named.goalDocument_group
#print axioms Fang.TptpCandidate.GoalDocument.Named.goalDocument_spec
#print axioms Fang.TptpCandidate.GoalDocument.Named.goalDocument_theorem
#print axioms Fang.TptpCandidate.GoalDocument.Named.goal_closed
#print axioms Fang.TptpCandidate.GoalDocument.Named.goal_entry
#print axioms Fang.TptpCandidate.GoalDocument.Named.goal_final_row_empty
#print axioms Fang.TptpCandidate.GoalDocument.Named.goal_group_sap
#print axioms Fang.TptpCandidate.GoalDocument.Named.goal_row_checked
#print axioms Fang.TptpCandidate.GoalDocument.Named.goal_row_local
#print axioms Fang.TptpCandidate.GoalDocument.Named.goal_rows
#print axioms Fang.TptpCandidate.GoalDocument.Named.premiseEntries_names
#print axioms Fang.TptpCandidate.Roles.Signed.prepareGoalNamed_models
#print axioms Fang.TptpCandidate.Roles.Signed.replayNamedTask_models_below
