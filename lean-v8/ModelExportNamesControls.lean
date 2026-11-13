/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel controls for finite model export, compiled separately to bound memory. -/
import ModelExportControlData

namespace Fang.TptpCandidate.FullFof.Model.ExportControls
open Fang.TptpCandidate.FullFof.Model

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

/-- An object whose content begins with `e` moves the fresh stem to `fang_e`. The objects `"e1"` and `"x"` are 006531
    and 0078. -/
theorem stem_avoids_objects :
    prints (bundle "fof(a,axiom,~ \"e1\" = \"x\")."
      "fang-model 1\ndomain 3\nfunction 006531 0 dense 0\nfunction 0078 0 dense 1\nend\n")
      "fof(fang_domain,fi_domain,\n    ! [X] : ( X = \"e1\" | X = \"x\" | X = \"fang_e2\" ) ).\n" = true := by
  cbv

end Fang.TptpCandidate.FullFof.Model.ExportControls
