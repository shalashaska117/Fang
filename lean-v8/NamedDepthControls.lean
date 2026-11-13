/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Controls only. The expanded entry with naming at the record's height: a
   shallow input prepares the same problem at heights 64 and 2,984, and a
   formula nested 100 deep is refused at 64 and prepared at 2,984. -/
import NamedDepthEntry
import NativeLimits

namespace Fang.TptpCandidate.FullFof.Integration.Named.DepthControls
open Aeneas.Std Fang.TptpCandidate.FullFof.Integration

def shallow : List UInt8 :=
  "fof(a, axiom, ![X, Y] : ((p(X) & q(X) & r(X)) | (s(Y) & t(Y) & u(Y)))).\n".toUTF8.toList

/-- `~(~(...(p(a))...))` with 100 negations. -/
def deep : List UInt8 :=
  ("fof(d, axiom, " ++ String.join (List.replicate 100 "~(") ++ "p(a)" ++
    String.join (List.replicate 100 ")") ++ ").\n").toUTF8.toList

def named (maxDepth : Nat) (bytes : List UInt8) : Except NamedError ReplayPrepared :=
  prepareNamedD Fang.NativeLimits.declarationLimit maxDepth bytes Fang.NativeLimits.byteLimit
    Fang.NativeLimits.replayLimits { bv := BitVec.ofNat _ 8 } Fang.NativeLimits.maximumPredicates
    Fang.NativeLimits.maximumLiterals

#guard match named 64 shallow, named 2984 shallow with
  | .ok low, .ok high =>
    reprStr low.problem == reprStr high.problem && low.predicateArities == high.predicateArities &&
      low.problem.length == 6 && low.predicateArities == [1, 1, 1, 1, 1, 1, 1]
  | _, _ => false

-- The refusal is the decoder's height bound: a resource error at the input stage.
#guard match named 64 deep with
  | .error (.replay (.input error)) => error.kind == .resource
  | _ => false

#guard match named 2984 deep with
  | .ok prepared => prepared.problem.length == 1
  | .error _ => false

end Fang.TptpCandidate.FullFof.Integration.Named.DepthControls
