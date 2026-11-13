/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel control for a function table written as a default with exceptions, compiled separately to bound memory.
   One unary function over two elements, under a layout that writes at most one cell in full. -/
import ModelExportControlData

namespace Fang.TptpCandidate.FullFof.Model.ExportControls
open Fang.TptpCandidate.FullFof.Model

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

/-- The two-cell table of `f` (66) prints as its most frequent value, `"e0"` on a tie, and the one cell that differs. -/
theorem default_document :
    prints (single oneCellLayout "fof(a,axiom,? [X] : f(X) = X)."
      "fang-model 1\ndomain 2\nfunction 66 1 dense 0 1\nend\n")
      ("fof(fang_domain,fi_domain,\n    ! [X] : ( X = \"e0\" | X = \"e1\" ) ).\n" ++
       "fof(fang_function_1,fi_functors,\n    f(\"e1\") = \"e1\" ).\n" ++
       "fof(fang_function_1_default,fi_functors,\n    ! [X1] : ( f(X1) = \"e0\" | X1 = \"e1\" ) ).\n")
      = true := by
  cbv

end Fang.TptpCandidate.FullFof.Model.ExportControls
