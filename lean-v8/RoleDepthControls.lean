/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Formula-depth and cited-task controls for the combined role entry. -/
import NamedCitedDepth
import NativeLimits

namespace Fang.TptpCandidate.Roles.Bundle.V3.Depth.Controls
open Aeneas.Std FullFof FullFof.Integration

private def deep := "fof(a, axiom, (" ++ String.intercalate " & " (List.replicate 100 "p") ++ ")).\n"
private def top : Coverage.Key := ⟨.base, ["input"]⟩
private def files (text : String) := [(top, text.toUTF8.toList)]
private def lim := Fang.NativeLimits.replayLimits
private def preds := Fang.NativeLimits.maximumPredicates
private def lits := Fang.NativeLimits.maximumLiterals
private def bytes := Fang.NativeLimits.byteLimit
private def proof := "(fang-proof 8 (preprocessing " ++ v8Marker ++ ") (input 0 0) (final 0))"

#guard (Bytes.decodeBytesLimitedD 65536 128 deep.toUTF8.toList bytes).toBool
#guard !(Bytes.decodeBytesLimitedD 65536 64 deep.toUTF8.toList bytes).toBool
#guard (frameBundleHashed 65536 128 (files deep) bytes).toBool
#guard !(frameBundleHashed 65536 64 (files deep) bytes).toBool

-- The deep premise is framed but not replayed when the proof cites none.
#guard match Named.acceptsGoalCited (frameBundleHashed 65536 128)
    (files (deep ++ "fof(g, conjecture, $true).\n")) bytes 0 [] proof lim 8#usize preds lits with
  | .ok item => item == ⟨0, 1⟩
  | _ => false

#guard match Named.acceptsInputsCited (frameBundleHashed 65536 128)
    (files (deep ++ "fof(z, axiom, $false).\n")) bytes [⟨0, 1⟩] proof lim 8#usize preds lits with
  | .ok () => true
  | _ => false

#guard !(frameBundleHashed 1 128 (files (deep ++ "fof(z, axiom, $false).\n")) bytes).toBool
#guard !(frameBundleHashed 65536 128 (files "fof(g, conjecture, p).\nfof(g, axiom, p).\n") bytes).toBool
#guard !(frameBundleHashed 65536 128 (files "cnf(g, conjecture, p).\n") bytes).toBool
#guard !(frameBundleHashed 65536 128 (files "fof(g, type, p).\n") bytes).toBool

end Fang.TptpCandidate.Roles.Bundle.V3.Depth.Controls
