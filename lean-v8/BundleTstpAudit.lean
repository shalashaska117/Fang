/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed audit module for bundle TSTP: the product entry and the group SAP
   at their expected types, over the revision-2 bundle meaning; the fast
   acceptance endpoint (as in `BundleFastAudit`, which this gate replaces with
   the light single-file controls); and audits of `step_mem` and `step_nodup`. -/
import BundleDocument

namespace Fang.QuantifiedEqualityTstp.Expanded.Bundle.Audit

open Aeneas.Std
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage (Key expand)
open Fang.TptpCandidate.FullFof.Coverage.BundleV8
open Fang.QuantifiedEqualityTstp.Expanded
open Fang.QuantifiedEqualityTstp.Expanded.Bundle

theorem expected_export_refuted {files : List (Key × List UInt8)} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize} {text : String}
    (success : exportBundleDocument files maximumBytes proof limits maximumPredicates maximumLiterals = .ok text) :
    (∃ bundle items, Coverage.FramerV2.frameBundle files maximumBytes = .ok bundle ∧
      Coverage.FramerV2.wellShaped bundle 17 = true ∧ expand bundle 17 = .ok items) ∧
      ¬ Coverage.FramerV2.ByteBundleSatisfiable files maximumBytes 17 :=
  exportBundleDocument_refuted success

theorem expected_group_sap {files : List (Key × List UInt8)} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize} {output : Output}
    (built : buildBundle files maximumBytes proof limits maximumPredicates maximumLiterals = .ok output)
    {stem : String} {functions : List Frontend.Symbol} {names : Body.Names}
    (named : attachBundle output stem functions = .ok names)
    {formula : NamedQuantifiedEquality.Formula}
    (formulaRun : Group.groupFormula names output.prepared.problem = .ok formula)
    (satisfiable : Coverage.FramerV2.ByteBundleSatisfiable files maximumBytes 17) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D), ∀ valuation, formula.Holds model valuation :=
  bundle_group_sap built named formulaRun satisfiable

theorem expected_fast_refuted {files : List (Key × List UInt8)} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize}
    (accepted : acceptsBundleFast files maximumBytes proof limits maximumPredicates maximumLiterals = .ok ()) :
    (∃ bundle items, Coverage.FramerV2.frameBundle files maximumBytes = .ok bundle ∧
      Coverage.FramerV2.wellShaped bundle 17 = true ∧ expand bundle 17 = .ok items) ∧
      ¬ Coverage.FramerV2.ByteBundleSatisfiable files maximumBytes 17 :=
  acceptsBundleFast_refuted accepted

theorem expected_fast_eq (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsBundleFast files maximumBytes proof limits maximumPredicates maximumLiterals =
      acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals :=
  acceptsBundleFast_eq files maximumBytes proof limits maximumPredicates maximumLiterals

#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.Audit.expected_export_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.Audit.expected_group_sap
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.Audit.expected_fast_refuted
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.Audit.expected_fast_eq
#print axioms Fang.TptpCandidate.FullFof.Coverage.step_mem
#print axioms Fang.TptpCandidate.FullFof.Coverage.step_nodup

end Fang.QuantifiedEqualityTstp.Expanded.Bundle.Audit
