/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel control for the countermodel document, compiled separately to bound memory. The input is a single nullary
   conjecture, so the kernel frames as little text as the goal path allows (`FINITE-MODEL-OUTPUT.md`, "Kernel controls
   and memory"). -/
import ModelExportControlData

namespace Fang.TptpCandidate.FullFof.Model.ExportControls
open Fang.TptpCandidate.FullFof.Model

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

/-- A countermodel document names the conjecture it falsifies. `p` is 70. -/
theorem goal_document :
    prints (goal "fof(g,conjecture,p)." "fang-model 1\ndomain 1\npredicate 70 0 dense 0\nend\n" 0)
      ("% The conjecture g is false in this model.\n" ++
       "fof(fang_domain,fi_domain,\n    ! [X] : X = \"e0\" ).\n" ++
       "fof(fang_predicate_1,fi_predicates,\n    ~ p ).\n") = true := by
  cbv

end Fang.TptpCandidate.FullFof.Model.ExportControls
