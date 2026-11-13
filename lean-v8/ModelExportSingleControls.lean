/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel controls for finite model export, compiled separately to bound memory. -/
import ModelExportControlData

namespace Fang.TptpCandidate.FullFof.Model.ExportControls
open Fang.TptpCandidate.FullFof.Model

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

theorem single_document : prints (single defaultLayout unitInput unitModel) unitDocument = true := by
  cbv

/-- The printed document has the meaning `Describes` gives it, so the theorem is not vacuous. -/
theorem single_document_meaning :
    ∃ values model, Integration.decodeBytesLimited Fang.NativeLimits.declarationLimit (bytesOf unitInput) 4096 =
        .ok values ∧ Describes defaultLayout model (source values) none unitDocument := by
  have run : single defaultLayout unitInput unitModel = .ok unitDocument := by
    have control := single_document
    cases result : single defaultLayout unitInput unitModel with
    | ok text =>
      rw [result] at control
      simp only [prints, beq_iff_eq] at control
      rw [control]
    | error problem =>
      rw [result] at control
      cases control
  obtain ⟨_, values, model, decoded, _, _, described⟩ := exportSingle_describes run
  exact ⟨values, model, decoded, described⟩

/-- A model the checker rejects gets no document. -/
theorem rejected_no_document :
    checkFailure (single defaultLayout unitInput
      "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 0\nend\n") = true := by
  cbv

end Fang.TptpCandidate.FullFof.Model.ExportControls
