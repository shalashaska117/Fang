/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Pure checks of the native role-v6 protocol before native compilation. -/
import SignedBundleNativeV6Core

namespace FangSignedBundleNativeV6.Controls
private def top : Fang.TptpCandidate.FullFof.Coverage.Key := ⟨.base, ["input"]⟩
private def files := [(top, "fof(a, axiom, p).\nfof(g, conjecture, $true).\n".toUTF8.toList)]
private def proof := "(fang-proof 8 (preprocessing " ++ Fang.TptpCandidate.FullFof.Integration.v8Marker ++
  ") (input 0 0) (final 0))"

#guard match check 128 8 (.goal 0) files ("(premises)\n" ++ proof) with
  | .ok text => (text.splitOn "accepted-goal 0 item 0 1").length == 2
  | _ => false

#guard match check 128 8 (.goal 0) files ("(premises (item 0 0) (item 0 0))\n" ++ proof) with
  | .error (code, message) => code == 3 && message == "certificate.premises"
  | _ => false

#guard match check 128 8 (.goal 0) files ("(premises (item 0 1))\n" ++ proof) with
  | .error (code, message) => code == 3 && message == "certificate.premises.citation:0:1"
  | _ => false

#guard match check 128 8 (.goal 0) files ("(premises  (item 0 0))\n" ++ proof) with
  | .error (code, message) => code == 3 && message == "certificate.premises"
  | _ => false

end FangSignedBundleNativeV6.Controls
