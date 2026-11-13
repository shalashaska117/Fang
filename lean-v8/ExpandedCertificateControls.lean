/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed version-8 envelope decoding controls: wrong versions, wrong or missing
   marker, truncated header, missing delimiter and trailing tokens. -/
import ExpandedEnvelope

namespace Fang.TptpCandidate.FullFof.Integration.V8Controls
open Fang.TptpCandidate.FullFof.Integration

def wrap (body : String) : String :=
  "(fang-proof 8 (preprocessing expanded-fof-equality-skolem-distributive-v1) " ++ body ++ ")"

set_option maxRecDepth 10000
set_option cbv.maxSteps 2000000

theorem minimal_decodes : decodesV8 (wrap "(input 0 0) (final 0)") = true := by cbv

theorem version7_rejects :
    decodesV8 "(fang-proof 7 (preprocessing nested-fof-equality-skolem-distributive-v1) (input 0 0) (final 0))" = false := by cbv

theorem version5_rejects :
    decodesV8 "(fang-proof 5 (preprocessing identity-cnf-equality-v1) (input 0 0) (final 0))" = false := by cbv

theorem version9_rejects :
    decodesV8 "(fang-proof 9 (preprocessing expanded-fof-equality-skolem-distributive-v1) (input 0 0) (final 0))" = false := by cbv

theorem v7_marker_rejects :
    decodesV8 "(fang-proof 8 (preprocessing nested-fof-equality-skolem-distributive-v1) (input 0 0) (final 0))" = false := by cbv

theorem missing_marker_rejects :
    decodesV8 "(fang-proof 8 (preprocessing) (input 0 0) (final 0))" = false := by cbv

theorem truncated_header_rejects :
    decodesV8 "(fang-proof 8 (preprocessing expanded-fof-equality-skolem-distributive-v1" = false := by cbv

theorem missing_close_rejects :
    decodesV8 "(fang-proof 8 (preprocessing expanded-fof-equality-skolem-distributive-v1) (input 0 0) (final 0)" = false := by cbv

theorem trailing_token_rejects : decodesV8 (wrap "(input 0 0) (final 0)" ++ " x") = false := by cbv

theorem final_out_of_range_rejects : decodesV8 (wrap "(input 0 0) (final 1)") = false := by cbv

#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.minimal_decodes
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.version7_rejects
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.version5_rejects
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.version9_rejects
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.v7_marker_rejects
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.missing_marker_rejects
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.truncated_header_rejects
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.missing_close_rejects
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.trailing_token_rejects
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Controls.final_out_of_range_rejects

end Fang.TptpCandidate.FullFof.Integration.V8Controls
