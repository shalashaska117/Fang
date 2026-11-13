/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Executable controls for checked names and named TSTP documents. -/
import NamedDocument
import NativeLimits

namespace Fang.QuantifiedEqualityTstp.NamedExport.Controls
open Aeneas.Std Fang.TptpCandidate.FullFof.Integration

private def input : List UInt8 :=
  ("fof(a, axiom, ![X, Y] : ((p(X) & q(X) & r(X)) | (s(Y) & t(Y) & u(Y)))).\n" ++
   "fof(z, axiom, $false).\n").toUTF8.toList
private def proof : String :=
  "(fang-proof 8 (preprocessing " ++ v8Marker ++ ") (input 0 6) (final 0))"
private def built := build Fang.NativeLimits.declarationLimit input Fang.NativeLimits.byteLimit proof
  Fang.NativeLimits.replayLimits 8#usize Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals

#guard match built with
  | .ok output =>
    (outputNames output).predicates.length == 7 &&
    ((outputNames output).predicates[6]?).map Frontend.Symbol.name == some "nmp0" &&
    (attach output (outputNames output)).toBool
  | _ => false

#guard match exportDocument Fang.NativeLimits.declarationLimit input Fang.NativeLimits.byteLimit proof
    Fang.NativeLimits.replayLimits 8#usize Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals "input" with
  | .ok text => (text.splitOn "status(sap)").length == 2 && (text.splitOn "nmp0").length > 1 &&
      (text.splitOn "$false").length > 1
  | _ => false

#guard match built with
  | .ok output =>
    let names := outputNames output
    !(attach output {names with predicates := names.predicates.dropLast ++ [⟨"p", some 1⟩]}).toBool
  | _ => false

#guard match built with
  | .ok output =>
    let names := outputNames output
    !(attach output {names with predicates := names.predicates.dropLast ++ [⟨"nmp0", some 2⟩]}).toBool
  | _ => false

#guard !(check [] [] ⟨[], [0], [0]⟩ ⟨[⟨"fresh", some 0⟩], [⟨"fresh", some 0⟩]⟩).toBool

#guard (exportNames [] [("nmp0", 0)] [] [0, 1]).predicates.map Frontend.Symbol.name == ["nmp0", "nm_p0"]

#guard match exportDocument Fang.NativeLimits.declarationLimit input Fang.NativeLimits.byteLimit "bad certificate"
    Fang.NativeLimits.replayLimits 8#usize Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals "input" with
  | .error _ => true
  | _ => false

end Fang.QuantifiedEqualityTstp.NamedExport.Controls
