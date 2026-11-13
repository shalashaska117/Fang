/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed audit module for the limits record on the bundle path: the acceptance and export endpoints of the hashed framer at any limit and of the native frame `limited`, at their expected types, and their equality with the earlier entries at 1,000 formulas per file. -/
import BundleDocumentLimit

namespace Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Audit

open Aeneas.Std
open Fang.TptpCandidate.FullFof
open Fang.TptpCandidate.FullFof.Coverage (Key expand)
open Fang.TptpCandidate.FullFof.Coverage.FramerLimit (frameBundle frameBundleHashed)

theorem expected_hashed_refuted (limit : Nat) {files : List (Key × List UInt8)} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize}
    (accepted : acceptsBundle (frameBundleHashed limit) files maximumBytes proof limits maximumPredicates
      maximumLiterals = .ok ()) :
    (∃ bundle items, frameBundle limit files maximumBytes = .ok bundle ∧
      Coverage.FramerV2.wellShaped bundle 17 = true ∧ expand bundle 17 = .ok items) ∧
      ¬ FramerLimit.ByteBundleSatisfiable (frameBundle limit) files maximumBytes 17 :=
  acceptsBundleHashed_refuted limit accepted

theorem expected_limited_refuted {files : List (Key × List UInt8)} {maximumBytes : Nat} {proof : String}
    (accepted : acceptsBundle limited files maximumBytes proof Fang.NativeLimits.replayLimits
      Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals = .ok ()) :
    (∃ bundle items, frameBundle 65536 files maximumBytes = .ok bundle ∧
      Coverage.FramerV2.wellShaped bundle 17 = true ∧ expand bundle 17 = .ok items) ∧
      ¬ FramerLimit.ByteBundleSatisfiable (frameBundle 65536) files maximumBytes 17 :=
  acceptsBundleLimited_refuted accepted

theorem expected_hashed_accepted (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    acceptsBundle (frameBundleHashed 1000) files maximumBytes proof limits maximumPredicates maximumLiterals =
      BundleV8.acceptsBundle files maximumBytes proof limits maximumPredicates maximumLiterals := by
  rw [acceptsBundle_hashed_accepted, BundleV8.acceptsBundleFast_eq]

theorem expected_export_hashed_refuted (limit : Nat) {files : List (Key × List UInt8)} {maximumBytes : Nat}
    {proof : String} {limits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize} {text : String}
    (success : Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument (frameBundleHashed limit) files
      maximumBytes proof limits maximumPredicates maximumLiterals = .ok text) :
    (∃ bundle items, frameBundle limit files maximumBytes = .ok bundle ∧
      Coverage.FramerV2.wellShaped bundle 17 = true ∧ expand bundle 17 = .ok items) ∧
      ¬ FramerLimit.ByteBundleSatisfiable (frameBundle limit) files maximumBytes 17 :=
  Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument_hashed_refuted limit success

theorem expected_export_hashed_accepted (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (maximumPredicates maximumLiterals : Usize) :
    Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument (frameBundleHashed 1000) files maximumBytes
      proof limits maximumPredicates maximumLiterals =
      Fang.QuantifiedEqualityTstp.Expanded.Bundle.exportBundleDocument files maximumBytes proof limits
        maximumPredicates maximumLiterals :=
  Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument_hashed_accepted files maximumBytes proof
    limits maximumPredicates maximumLiterals

/-- With framer revision 2 as the frame, the meaning is the revision-2 bundle meaning. -/
theorem expected_meaning_revision_two (files : List (Key × List UInt8)) (maximumBytes fuel : Nat) :
    FramerLimit.ByteBundleSatisfiable (frameBundle 1000) files maximumBytes fuel ↔
      Coverage.FramerV2.ByteBundleSatisfiable files maximumBytes fuel := by
  have same : frameBundle 1000 = Coverage.FramerV2.frameBundle := by
    funext files maximum
    exact FramerLimit.frameBundle_accepted files maximum
  rw [same, FramerLimit.byteBundleSatisfiable_revision_two]

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Audit.expected_hashed_refuted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Audit.expected_limited_refuted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Audit.expected_hashed_accepted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Audit.expected_export_hashed_refuted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Audit.expected_export_hashed_accepted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Audit.expected_meaning_revision_two

end Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Audit
