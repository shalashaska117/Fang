/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed version-8 checkProblem controls: the envelope with the producer's exact
   header layout, the signature gate and the ordered checker on small problems. -/
import ExpandedEnvelope

namespace Fang.TptpCandidate.FullFof.Integration.V8Checks
open Fang.TptpCandidate.FullFof.Integration

def wrap (body : String) : String :=
  "(fang-proof 8 (preprocessing expanded-fof-equality-skolem-distributive-v1) " ++ body ++ ")"

/-- The exact header bytes the Rust producer writes, with its newlines. -/
def producerWrap (body : String) : String :=
  "(fang-proof 8\n  (preprocessing expanded-fof-equality-skolem-distributive-v1)\n" ++ body ++ ")\n"

def problem : Fang.Equality.Problem :=
  [[⟨true, .equal (.app 0 []) (.app 1 [])⟩],
   [⟨false, .equal (.app 2 [.app 0 []]) (.app 2 [.app 1 []])⟩]]

def derivation : String :=
  "(input 0 0) (input 1 1) (paramodulate 2 0 1 0 0 (equality-left) (path 0) forward (subst) (clause (neg (eq (f 2 (f 1)) (f 2 (f 1)))))) (eq-resolve 3 2 (clause) (clause) (f 2 (f 1)) (f 2 (f 1)) (subst) (clause)) (final 3)"

set_option maxRecDepth 10000
set_option cbv.maxSteps 2000000

theorem ordered_derivation_accepts :
    checkProblem problem [0, 0, 1] [] (wrap derivation) = .ok () := by cbv

theorem producer_layout_accepts :
    checkProblem [[]] [] [] (producerWrap "  (input 0 0)\n  (final 0)\n") = .ok () := by cbv

theorem signature_rejects :
    checkProblem problem [0, 0] [] (wrap derivation) = .error .signature := by cbv

theorem nonempty_endpoint_rejects :
    (match checkProblem problem [0, 0, 1] [] (wrap "(input 0 0) (final 0)") with
     | .error (.inference _) => true
     | _ => false) = true := by cbv

#print axioms Fang.TptpCandidate.FullFof.Integration.V8Checks.ordered_derivation_accepts
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Checks.producer_layout_accepts
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Checks.signature_rejects
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Checks.nonempty_endpoint_rejects

end Fang.TptpCandidate.FullFof.Integration.V8Checks
