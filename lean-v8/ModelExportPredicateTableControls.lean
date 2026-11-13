/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel controls for a predicate table written as a default with exceptions and for an export that fails while the
   model stays accepted, compiled separately to bound memory. One unary predicate over two elements. -/
import ModelExportControlData

namespace Fang.TptpCandidate.FullFof.Model.ExportControls
open Fang.TptpCandidate.FullFof.Model

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

def someInput : String := "fof(a,axiom,? [X] : q(X))."
def someModel : String := "fang-model 1\ndomain 2\npredicate 71 1 dense 0 1\nend\n"

/-- The two-cell table of `q` (71) prints as false, the value it takes first on a tie, and the one cell where it
    holds. -/
theorem predicate_default_document :
    prints (single oneCellLayout someInput someModel)
      ("fof(fang_domain,fi_domain,\n    ! [X] : ( X = \"e0\" | X = \"e1\" ) ).\n" ++
       "fof(fang_predicate_1,fi_predicates,\n    q(\"e1\") ).\n" ++
       "fof(fang_predicate_1_default,fi_predicates,\n    ! [X1] : ( ~ q(X1) | X1 = \"e1\" ) ).\n")
      = true := by
  cbv

/-- A table too large to enumerate under the layout fails the export, while the checker still accepts the model. -/
theorem export_fails_model_accepted :
    documentFailure (single { oneCellLayout with enumeration := 1 } someInput someModel) =
        some "resource.export.table" ∧
      (acceptsSingle defaultLimits Fang.NativeLimits.declarationLimit (bytesOf someInput) 4096 someModel).toBool =
        true := by
  cbv

end Fang.TptpCandidate.FullFof.Model.ExportControls
