/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel controls for finite model export, compiled separately to bound memory. -/
import ModelExportControlData

namespace Fang.TptpCandidate.FullFof.Model.ExportControls
open Fang.TptpCandidate.FullFof.Model

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

/-- The same model through the role frame without conjectures. -/
theorem inputs_document : prints (inputs unitInput unitModel) unitDocument = true := by
  cbv

end Fang.TptpCandidate.FullFof.Model.ExportControls
