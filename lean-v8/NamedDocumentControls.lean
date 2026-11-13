/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Named goal and include-bundle document rendering controls. -/
import NamedGoalDocument
import NamedBundleDocument
import NativeLimits

namespace Fang.QuantifiedEqualityTstp.NamedDocumentControls
open Aeneas.Std Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration

private def input : String :=
  "fof(a, axiom, ![X, Y] : ((p(X) & q(X) & r(X)) | (s(Y) & t(Y) & u(Y)))).\n"
private def proof : String :=
  "(fang-proof 8 (preprocessing " ++ v8Marker ++ ") (input 0 6) (final 0))"
private def top : Coverage.Key := ⟨.base, ["input"]⟩
private def ax : Coverage.Key := ⟨.base, ["axioms.ax"]⟩
private def files := [(top, "include('axioms.ax').\nfof(z, axiom, $false).\n".toUTF8.toList),
  (ax, input.toUTF8.toList)]

#guard match Fang.TptpCandidate.GoalDocument.Named.exportGoalDocument Fang.NativeLimits.declarationLimit
    (input ++ "fof(g, conjecture, $true).\n").toUTF8.toList Fang.NativeLimits.byteLimit 0 proof
    Fang.NativeLimits.replayLimits 8#usize Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals "input" with
  | .ok text => (text.splitOn "status(sap)").length == 2 && (text.splitOn "nmp0").length > 1 &&
      (text.splitOn "conjecture").length > 1
  | _ => false

#guard match Expanded.BundleLimit.Named.exportBundleDocument Coverage.BundleLimit.limited files
    Fang.NativeLimits.byteLimit proof Fang.NativeLimits.replayLimits 8#usize Fang.NativeLimits.maximumPredicates
    Fang.NativeLimits.maximumLiterals with
  | .ok text => (text.splitOn "status(sap)").length == 2 && (text.splitOn "nmp0").length > 1 &&
      (text.splitOn "axioms.ax").length > 1
  | _ => false

#guard match Expanded.BundleLimit.Named.exportBundleDocument Coverage.BundleLimit.limited files
    Fang.NativeLimits.byteLimit "bad certificate" Fang.NativeLimits.replayLimits 8#usize Fang.NativeLimits.maximumPredicates
    Fang.NativeLimits.maximumLiterals with
  | .error _ => true
  | _ => false

end Fang.QuantifiedEqualityTstp.NamedDocumentControls
