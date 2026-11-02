/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The byte premises of `acceptsBundle_single` discharged on one plain file,
   over the framer and the accepted decoder only. -/
import BundleSinglePremises

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single

open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2

def commentsEquality : List UInt8 :=
  bytesOf "% header\nfof(e,axiom,![X]:(f(X) = X)). /* note */ cnf(n,axiom,f(a) != a).\n"

set_option maxRecDepth 20000 in
theorem commentsEquality_premises : SinglePremises commentsEquality := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.commentsEquality_premises

end Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single
