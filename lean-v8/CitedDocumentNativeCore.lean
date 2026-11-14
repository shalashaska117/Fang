import CitedGoalSemantics
import CitedInputsDocument
import SignedBundleNativeV6Core
import NativeLimits

namespace FangCitedDocumentNative
open Fang.TptpCandidate Roles.Bundle Roles.Bundle.V3 Roles.Bundle.V3.Depth

inductive Task where
  | goal (index : Nat)
  | inputs

def render (task : Task) (files : List (FullFof.Coverage.Key × List UInt8)) (envelope : String) : Except String String := do
  let some parsed := FangSignedBundleNativeV6.splitPremises envelope
    | .error "export-error: cited certificate envelope is required"
  let (cited, proof) ← parsed.mapError (fun _ => "export-error: invalid cited certificate envelope")
  let frame := frameBundleHashed Fang.NativeLimits.declarationLimit Fang.NativeLimits.formulaDepthLimit
  let threshold : Aeneas.Std.Usize := { bv := BitVec.ofNat _ Fang.NativeLimits.namingThreshold }
  match task with
  | .goal index =>
    CitedDocument.exportGoalDocument frame Fang.NativeLimits.formulaDepthLimit files
      Fang.NativeLimits.byteLimit index cited proof Fang.NativeLimits.replayLimits threshold
      Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals
  | .inputs =>
    CitedDocument.Inputs.exportDocument frame Fang.NativeLimits.formulaDepthLimit files
      Fang.NativeLimits.byteLimit cited proof Fang.NativeLimits.replayLimits threshold
      Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals

def run (task : Task) (proofPath : String) (fileArguments : List String) : IO UInt32 := do
  match ← FangSignedBundleNativeV6.readText Fang.NativeLimits.certificateLimit proofPath with
  | .error error => FangSignedBundleNativeV6.reject (FangSignedBundleNativeV6.readMessage "certificate" error)
  | .ok envelope =>
    match ← FangSignedBundleNativeV6.readFiles fileArguments 0 with
    | .error error => FangSignedBundleNativeV6.reject error
    | .ok files =>
      match render task files envelope with
      | .error message => FangSignedBundleNativeV6.reject (if message.startsWith "resource-exhaustion" then 4 else 7, message)
      | .ok document =>
        IO.print document
        return 0

end FangCitedDocumentNative
