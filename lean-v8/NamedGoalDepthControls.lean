import NamedGoalDocumentDepth
import NativeLimits

namespace Fang.TptpCandidate.GoalDocument.NamedDepth.Controls
open Aeneas.Std FullFof.Integration
-- The selected goal is true; the second goal tests deep decoding and source-row export.
private def deep := "fof(g, conjecture, $true).\nfof(other, conjecture, (" ++ String.intercalate " & " (List.replicate 100 "$true") ++ ")).\n"
private def lim : FangOriginalReplay.Limits := {
  Fang.NativeLimits.replayLimits with
  skolem := { Fang.NativeLimits.replayLimits.skolem with
    core := { Fang.NativeLimits.replayLimits.skolem.core with max_formula_depth := 256#usize } }
  removal := { Fang.NativeLimits.replayLimits.removal with max_formula_depth := 256#usize }
  clausification := { Fang.NativeLimits.replayLimits.clausification with max_formula_depth := 256#usize } }
private def proof := "(fang-proof 8 (preprocessing " ++ v8Marker ++ ") (input 0 0) (final 0))"
private def exported (depth : Nat) := exportGoalDocument 65536 depth deep.toUTF8.toList
  Fang.NativeLimits.byteLimit 0 proof lim 8#usize Fang.NativeLimits.maximumPredicates
  Fang.NativeLimits.maximumLiterals "input"
#guard (exported 128).toBool
#guard !(exported 64).toBool
#guard match exported 128 with
  | .ok text => (text.splitOn "status(sap)").length == 2 && (text.splitOn "conjecture").length > 1
  | _ => false
#guard !(exportGoalDocument 65536 128 deep.toUTF8.toList Fang.NativeLimits.byteLimit 0
  "bad certificate" lim 8#usize Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals "input").toBool
end Fang.TptpCandidate.GoalDocument.NamedDepth.Controls
