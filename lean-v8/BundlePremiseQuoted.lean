/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The byte premises of `acceptsBundle_single` discharged on one plain file,
   over the framer and the accepted decoder only. -/
import BundleSinglePremises

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single

open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2

def quotedNames : List UInt8 := bytesOf "fof('a b',axiom,?[Y]:r(Y,'c d')). fof(2,axiom,~r(e,'c d') | $true)."

set_option maxRecDepth 20000 in
theorem quotedNames_premises : SinglePremises quotedNames := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.quotedNames_premises

end Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single
