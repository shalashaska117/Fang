/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Controls only. The named single-file document at a height parameter, under the
   final record: a formula nested 100 deep with its refutation is refused at
   height 64 and exported at height 2,984, and a pair that needs naming exports
   its named predicate under a fresh name. -/
import NamedDocumentDepth
import NativeLimits

namespace Fang.QuantifiedEqualityTstp.NamedExport.DepthControls
open Aeneas.Std Fang.QuantifiedEqualityTstp.NamedExport

def deep : List UInt8 :=
  ("fof(d, axiom, " ++ String.join (List.replicate 100 "~(") ++ "p(a)" ++
    String.join (List.replicate 100 ")") ++ ").\nfof(n, axiom, ~p(a)).\n").toUTF8.toList

def deepProof : String :=
  "(fang-proof 8 (preprocessing expanded-fof-equality-skolem-distributive-v1) (input 0 0) (input 1 1) " ++
    "(resolve 2 0 0 1 0 (subst) (clause)) (final 2))"

def disjunction : List UInt8 :=
  ("fof(a, axiom, ![X, Y] : ((p(X) & q(X) & r(X)) | (s(Y) & t(Y) & u(Y)))).\n" ++
    "fof(b, axiom, ~p(c)).\nfof(d, axiom, ~s(c)).\n").toUTF8.toList

/-- The certificate the expanded producer with naming wrote for `disjunction`. -/
def disjunctionProof : String :=
  "(fang-proof 8 (preprocessing expanded-fof-equality-skolem-distributive-v1) (input 0 0) (input 1 3) " ++
    "(input 2 6) (input 3 7) (resolve 4 3 0 0 1 (subst (1 (v 0)) (3 (f 0))) (clause (pos (pred 6 (v 0))))) " ++
    "(resolve 5 1 1 2 0 (subst (0 (f 0))) (clause (neg (pred 6 (f 0))))) " ++
    "(resolve 6 5 0 4 0 (subst (1 (f 0))) (clause)) (final 6))"

def exported (maxDepth : Nat) (bytes : List UInt8) (proof file : String) : Except String String :=
  exportDocumentD Fang.NativeLimits.declarationLimit maxDepth bytes Fang.NativeLimits.byteLimit proof
    Fang.NativeLimits.replayLimits { bv := BitVec.ofNat _ 8 } Fang.NativeLimits.maximumPredicates
    Fang.NativeLimits.maximumLiterals file

#guard match exported 64 deep deepProof "deep.p" with
  | .error message => message == "export-error: the certificate is not accepted for these bytes"
  | .ok _ => false

#guard match exported 2984 deep deepProof "deep.p" with
  | .ok text => (text.splitOn "fof ( d , axiom").length == 2 && (text.splitOn "($false)").length == 2
  | .error _ => false

#guard match exported 2984 disjunction disjunctionProof "disjunction.p" with
  | .ok text => (text.splitOn "nmp0").length > 1 && (text.splitOn "($false)").length == 2
  | .error _ => false

end Fang.QuantifiedEqualityTstp.NamedExport.DepthControls
