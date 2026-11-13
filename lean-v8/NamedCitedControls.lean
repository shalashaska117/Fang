/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Cited-premise controls with naming, full-goal identities and reduced tables. -/
import NamedCited
import NativeLimits

namespace Fang.TptpCandidate.NamedCitedControls
open Aeneas.Std FullFof FullFof.Integration Roles.Bundle.V3

private def input : String :=
  "fof(a, axiom, ![X, Y] : ((p(X) & q(X) & r(X)) | (s(Y) & t(Y) & u(Y)))).\n"
private def top : Coverage.Key := ⟨.base, ["input"]⟩
private def files (text : String) := [(top, text.toUTF8.toList)]
private def lim := Fang.NativeLimits.replayLimits
private def preds := Fang.NativeLimits.maximumPredicates
private def lits := Fang.NativeLimits.maximumLiterals
private def bytes := Fang.NativeLimits.byteLimit
private def proof (index : Nat) : String :=
  "(fang-proof 8 (preprocessing " ++ v8Marker ++ ") (input 0 " ++ toString index ++ ") (final 0))"

#guard match Named.prepareGoalCited limited (files (input ++ "fof(g, conjecture, $true).\n")) bytes 0
    [⟨0, 0⟩] lim 8#usize preds lits with
  | .ok p => p.item == ⟨0, 1⟩ && p.replay.problem.length == 7 && p.replay.predicateArities.length == 7
  | _ => false

#guard match Named.acceptsGoalCited limited (files (input ++ "fof(g, conjecture, $true).\n")) bytes 0
    [⟨0, 0⟩] (proof 6) lim 8#usize preds lits with
  | .ok item => item == ⟨0, 1⟩
  | _ => false

#guard match Named.prepareGoalCited limited (files (input ++ "fof(g, conjecture, $true).\n")) bytes 0
    [] lim 8#usize preds lits with
  | .ok p => p.item == ⟨0, 1⟩ && p.replay.problem.length == 1 && p.replay.predicateArities.isEmpty
  | _ => false

#guard match Named.acceptsInputsCited limited (files (input ++ "fof(z, axiom, $false).\n")) bytes
    [⟨0, 1⟩] (proof 0) lim 8#usize preds lits with
  | .ok () => true
  | _ => false

#guard match Named.prepareGoalCited limited (files (input ++ "fof(g, conjecture, $true).\n")) bytes 0
    [⟨0, 1⟩] lim 8#usize preds lits with
  | .error (.citation item) => item == ⟨0, 1⟩
  | _ => false

#guard match Named.prepareInputsCited limited (files input) bytes [⟨9, 9⟩] lim 8#usize preds lits with
  | .error (.citation item) => item == ⟨9, 9⟩
  | _ => false

#guard match Named.prepareInputsCited limited
    (files ("fof(o, axiom, \"a\" = \"b\").\nfof(z, axiom, $false).\n")) bytes [⟨0, 1⟩] lim 8#usize preds lits with
  | .ok p => p.problem.length == 1 && p.functionArities.isEmpty
  | _ => false

end Fang.TptpCandidate.NamedCitedControls
