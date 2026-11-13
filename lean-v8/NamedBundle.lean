/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Bundle acceptance with naming, over the same sound framers and meanings as
   BundleReplayLimit. Naming changes the replay after the numeric input is read. -/
import NamedCore
import BundleReplayLimit

namespace Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Named

open Aeneas.Std
open Fang.TptpCandidate.FullFof.Integration
open FangQuantifiedEqualityReplay (bind_success mapError_success)
open FramerLimit (Frame FrameSound ByteBundleSatisfiable frameBundle frameBundleHashed)
open BundleV8 (bundleFuel)

inductive ReplayError where
  | bundle : BundleV8.BundleError → ReplayError
  | replay : Integration.Named.NamedError → ReplayError

inductive AcceptError where
  | replay : ReplayError → AcceptError
  | certificate : CertificateError → AcceptError

def prepareBundle (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except ReplayError ReplayPrepared := do
  let numeric ← (bundleNumeric frame files maximumBytes).mapError .bundle
  (Integration.Named.replayNamedFrom numeric limits threshold maximumPredicates maximumLiterals).mapError .replay

def acceptsBundle (frame : Frame) (files : List (Key × List UInt8)) (maximumBytes : Nat) (proof : String)
    (limits : FangOriginalReplay.Limits) (threshold maximumPredicates maximumLiterals : Usize) :
    Except AcceptError Unit := do
  let prepared ← (prepareBundle frame files maximumBytes limits threshold maximumPredicates maximumLiterals).mapError
    .replay
  (checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof).mapError .certificate

theorem acceptsBundle_original_unsat {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsBundle frame files maximumBytes proof limits threshold maximumPredicates maximumLiterals =
      .ok ()) :
    ¬ ByteBundleSatisfiable frame files maximumBytes bundleFuel := by
  obtain ⟨prepared, prepareRun, checked⟩ := bind_success accepted
  obtain ⟨numeric, numericRun, replayRun⟩ := bind_success (mapError_success prepareRun)
  obtain ⟨parsed, _, _, _, refuted⟩ := checkProblem_success (mapError_success checked)
  have numericOk := mapError_success numericRun
  exact bundleNumeric_unsat frameSound numericOk
    (Integration.Named.replayNamedFrom_check_unsat (bundleNumeric_below frameSound numericOk)
      (mapError_success replayRun) parsed refuted)

theorem acceptsBundle_refuted {frame : Frame} (frameSound : FrameSound frame)
    {files maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsBundle frame files maximumBytes proof limits threshold maximumPredicates maximumLiterals =
      .ok ()) :
    BundleRefuted frame files maximumBytes bundleFuel := by
  refine ⟨?_, acceptsBundle_original_unsat frameSound accepted⟩
  obtain ⟨prepared, prepareRun, _⟩ := bind_success accepted
  obtain ⟨numeric, numericRun, _⟩ := bind_success (mapError_success prepareRun)
  obtain ⟨bundle, items, _, framed, shaped, expanded, _, _⟩ := bundleNumeric_witness (mapError_success numericRun)
  exact ⟨bundle, items, framed, shaped, expanded⟩

theorem acceptsBundleHashed_refuted (limit : Nat)
    {files maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsBundle (frameBundleHashed limit) files maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    BundleRefuted (frameBundle limit) files maximumBytes bundleFuel := by
  rw [FramerLimit.frameBundleHashed_eq] at accepted
  exact acceptsBundle_refuted (FramerLimit.frameBundle_sound limit) accepted

theorem acceptsBundleLimited_refuted {files maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsBundle limited files maximumBytes proof limits threshold maximumPredicates maximumLiterals =
      .ok ()) :
    BundleRefuted limitedSpecification files maximumBytes bundleFuel :=
  acceptsBundleHashed_refuted Fang.NativeLimits.declarationLimit accepted

end Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Named
