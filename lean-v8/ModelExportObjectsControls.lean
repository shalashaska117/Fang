/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel control for distinct objects in a bundle, compiled separately to bound memory. -/
import ModelExportControlData

namespace Fang.TptpCandidate.FullFof.Model.ExportControls
open Fang.TptpCandidate.FullFof.Model

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

/-- Input distinct objects name their elements, and a table prints with those names. `f` is 66, the objects `"a"` and
    `"b"` are 0061 and 0062. Fresh names next to objects are the Names control's. -/
theorem bundle_objects_document :
    prints (bundle "fof(a,axiom,f(\"a\") = \"b\")."
      "fang-model 1\ndomain 2\nfunction 0061 0 dense 0\nfunction 0062 0 dense 1\nfunction 66 1 dense 1 0\nend\n")
      ("fof(fang_domain,fi_domain,\n    ! [X] : ( X = \"a\" | X = \"b\" ) ).\n" ++
       "fof(fang_function_1,fi_functors,\n    ( f(\"a\") = \"b\"\n    & f(\"b\") = \"a\" ) ).\n")
      = true := by
  cbv

end Fang.TptpCandidate.FullFof.Model.ExportControls
