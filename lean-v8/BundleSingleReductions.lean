/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The single-file reduction to the accepted version-8 `accepts` from the
   byte premises, and the reduction for each of the four files whose premises
   are discharged in their own modules. -/
import BundleReplay
import BundlePremisePlainCnf
import BundlePremisePlainFof
import BundlePremiseComments
import BundlePremiseQuoted

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single

open Aeneas.Std
open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2
open Fang.TptpCandidate.FullFof.Coverage.BundleV8

theorem single_of_premises {bytes : List UInt8} (premises : SinglePremises bytes) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle [(top, bytes)] 4096 proof limits maximumPredicates maximumLiterals =
      (accepts bytes 4096 proof limits maximumPredicates maximumLiterals).mapError liftError := by
  obtain ⟨decoded, framed, encodedSome, noObjects⟩ := premises
  obtain ⟨input, encoded⟩ := Option.isSome_iff_exists.mp encodedSome
  exact acceptsBundle_single proof limits maximumPredicates maximumLiterals decoded encoded framed noObjects
    top_wellFormed

theorem plainCnf_reduces (proof : String) (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle [(top, plainCnf)] 4096 proof limits maximumPredicates maximumLiterals =
      (accepts plainCnf 4096 proof limits maximumPredicates maximumLiterals).mapError liftError :=
  single_of_premises plainCnf_premises proof limits maximumPredicates maximumLiterals

theorem plainFof_reduces (proof : String) (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle [(top, plainFof)] 4096 proof limits maximumPredicates maximumLiterals =
      (accepts plainFof 4096 proof limits maximumPredicates maximumLiterals).mapError liftError :=
  single_of_premises plainFof_premises proof limits maximumPredicates maximumLiterals

theorem commentsEquality_reduces (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle [(top, commentsEquality)] 4096 proof limits maximumPredicates maximumLiterals =
      (accepts commentsEquality 4096 proof limits maximumPredicates maximumLiterals).mapError liftError :=
  single_of_premises commentsEquality_premises proof limits maximumPredicates maximumLiterals

theorem quotedNames_reduces (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle [(top, quotedNames)] 4096 proof limits maximumPredicates maximumLiterals =
      (accepts quotedNames 4096 proof limits maximumPredicates maximumLiterals).mapError liftError :=
  single_of_premises quotedNames_premises proof limits maximumPredicates maximumLiterals

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.single_of_premises
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.plainCnf_reduces
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.plainFof_reduces
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.commentsEquality_reduces
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single.quotedNames_reduces

end Fang.TptpCandidate.FullFof.Coverage.BundleV8.Single
