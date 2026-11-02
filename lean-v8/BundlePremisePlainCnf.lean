/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The byte premises of `acceptsBundle_single` discharged on one plain file,
   over the framer and the accepted decoder only. -/
import BundleSinglePremises

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single

open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2

def plainCnf : List UInt8 := bytesOf "cnf(a,axiom,p(X) | ~q(X)). cnf(b,axiom,q(c)). cnf(c,axiom,~p(c))."

set_option maxRecDepth 20000 in
theorem plainCnf_premises : SinglePremises plainCnf := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.plainCnf_premises

end Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single
