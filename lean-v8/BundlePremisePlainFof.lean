/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The byte premises of `acceptsBundle_single` discharged on one plain file,
   over the framer and the accepted decoder only. -/
import BundleSinglePremises

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single

open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2

def plainFof : List UInt8 := bytesOf "fof(a,axiom,![X]:(p(X) <=> q(X))). fof(b,axiom,p(c)). fof(c,axiom,~q(c))."

set_option maxRecDepth 20000 in
theorem plainFof_premises : SinglePremises plainFof := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.plainFof_premises

end Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single
