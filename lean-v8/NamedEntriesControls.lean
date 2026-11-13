/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Executable controls for the signed and bundle entries with naming. -/
import NamedBundle
import NamedRoleBundle
import NativeLimits

namespace Fang.TptpCandidate.NamedEntriesControls
open Aeneas.Std FullFof FullFof.Integration

private def input : String :=
  "fof(a, axiom, ![X, Y] : ((p(X) & q(X) & r(X)) | (s(Y) & t(Y) & u(Y)))).\n"
private def falseInput := input ++ "fof(z, axiom, $false).\n"
private def goalInput := input ++ "fof(z, conjecture, $true).\n"
private def top : Coverage.Key := ⟨.base, ["input"]⟩
private def ax : Coverage.Key := ⟨.base, ["ax.ax"]⟩
private def files (text : String) := [(top, text.toUTF8.toList)]
private def includes :=
  [(top, "include('ax.ax').\nfof(z, conjecture, $true).\n".toUTF8.toList),
   (ax, input.toUTF8.toList)]
private def proof : String :=
  "(fang-proof 8 (preprocessing " ++ v8Marker ++ ") (input 0 6) (final 0))"
private def wrong : String :=
  "(fang-proof 8 (preprocessing " ++ v8Marker ++ ") (input 0 0) (final 0))"
private def lim := Fang.NativeLimits.replayLimits
private def preds := Fang.NativeLimits.maximumPredicates
private def lits := Fang.NativeLimits.maximumLiterals
private def bytes := Fang.NativeLimits.byteLimit
private def decls := Fang.NativeLimits.declarationLimit

#guard match Roles.Signed.prepareInputsNamed decls input.toUTF8.toList bytes lim 8#usize preds lits with
  | .ok p => p.problem.length == 6 && p.predicateArities == [1, 1, 1, 1, 1, 1, 1]
  | _ => false

#guard match Coverage.BundleLimit.Named.prepareBundle Coverage.BundleLimit.limited (files input) bytes
    lim 8#usize preds lits with
  | .ok p => p.problem.length == 6 && p.predicateArities == [1, 1, 1, 1, 1, 1, 1]
  | _ => false

#guard match Roles.Bundle.V3.Named.prepareGoal Roles.Bundle.V3.limited includes bytes 0 lim 8#usize preds lits with
  | .ok p => p.replay.problem.length == 7 && p.replay.predicateArities == [1, 1, 1, 1, 1, 1, 1]
  | _ => false

#guard match Roles.Signed.acceptsInputsNamed decls falseInput.toUTF8.toList bytes proof lim 8#usize preds lits with
  | .ok () => true
  | _ => false

#guard match Roles.Signed.acceptsGoalNamed decls goalInput.toUTF8.toList bytes 0 proof lim 8#usize preds lits with
  | .ok () => true
  | _ => false

#guard match Coverage.BundleLimit.Named.acceptsBundle Coverage.BundleLimit.limited (files falseInput) bytes proof
    lim 8#usize preds lits with
  | .ok () => true
  | _ => false

#guard match Roles.Bundle.V3.Named.acceptsInputs Roles.Bundle.V3.limited (files falseInput) bytes proof
    lim 8#usize preds lits with
  | .ok () => true
  | _ => false

#guard match Roles.Bundle.V3.Named.acceptsGoal Roles.Bundle.V3.limited includes bytes 0 proof lim 8#usize preds lits with
  | .ok _ => true
  | _ => false

#guard match Roles.Bundle.V3.Named.acceptsGoal Roles.Bundle.V3.limited includes bytes 0 wrong lim 8#usize preds lits with
  | .error (.certificate (.inference _)) => true
  | _ => false

#guard match Roles.Bundle.V3.Named.prepareInputs Roles.Bundle.V3.limited (files goalInput) bytes lim 8#usize preds lits with
  | .error .goalsPresent => true
  | _ => false

#guard match Roles.Bundle.V3.Named.prepareGoal Roles.Bundle.V3.limited includes bytes 1 lim 8#usize preds lits with
  | .error .noGoal => true
  | _ => false

#guard match Roles.Bundle.V3.Named.prepareInputs Roles.Bundle.V3.limited
    (files (input ++ "fof(d, axiom, \"a\" = \"b\").\n")) bytes lim 8#usize preds lits with
  | .ok p => p.problem.length == 8 && p.functionArities == [0, 0]
  | _ => false

#guard match Roles.Bundle.V3.Named.prepareInputs Roles.Bundle.V3.limited (files input) bytes lim 1000000#usize preds lits,
    Roles.Bundle.V3.prepareInputs Roles.Bundle.V3.limited (files input) bytes lim preds lits with
  | .ok p, .ok old => reprStr p.problem == reprStr old.problem && p.problem.length == 9 &&
      p.functionArities == old.functionArities && p.predicateArities == old.predicateArities
  | _, _ => false

end Fang.TptpCandidate.NamedEntriesControls
