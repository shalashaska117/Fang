/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed audit module: the bundle version-8 endpoints at their expected types. -/
import BundleReplay

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8.Audit

open Aeneas.Std
open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2
open Fang.TptpCandidate.FullFof.Coverage.BundleV8

theorem expected_bundle_unsat {files : List (Key × List UInt8)} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize}
    (accepted : acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    ¬ ByteBundleSatisfiable files maximumBytes 17 :=
  acceptsBundle_original_unsat accepted

theorem expected_bundle_refuted {files : List (Key × List UInt8)} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize}
    (accepted : acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    (∃ bundle items, frameBundle files maximumBytes = .ok bundle ∧ wellShaped bundle 17 = true ∧
      expand bundle 17 = .ok items) ∧ ¬ ByteBundleSatisfiable files maximumBytes 17 :=
  acceptsBundle_refuted accepted

theorem expected_single_file {bytes : List UInt8} {maximumBytes : Nat} {values : List Declaration}
    {input : NumericInput} {key : Key} (proof : String) (limits : FangOriginalReplay.Limits)
    (maximumPredicates maximumLiterals : Usize)
    (decoded : CnfBoolean.decodeBytes bytes maximumBytes = .ok values)
    (encoded : readInput values = some input)
    (framed : frameFile bytes maximumBytes = .ok (values.map .formula))
    (noObjects : objectNames values = [])
    (wellFormed : keyWellFormed key = true) :
    acceptsBundle [(key, bytes)] maximumBytes proof limits maximumPredicates maximumLiterals =
      (accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals).mapError liftError :=
  acceptsBundle_single proof limits maximumPredicates maximumLiterals decoded encoded framed noObjects wellFormed

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Audit.expected_bundle_unsat
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Audit.expected_bundle_refuted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Audit.expected_single_file

end Fang.TptpCandidate.FullFof.Coverage.BundleV8.Audit
