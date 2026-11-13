import Fang.CertificateInput

/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Compiled parser tests. These checks do not produce kernel proofs of parsing.
-/

namespace Fang.FrontendTests

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def exampleInput : String :=
  "cnf(c0,axiom,(p(X)|p(Y)|p(X))).\ncnf(c1,axiom,(~p(a))).\n"

def exampleProof : String :=
  "(fang-proof 1 (input 0 0) (input 1 1) " ++
  "(factor 2 0 0 1 (subst (1 (v 0))) (clause (pos 0 (v 0)))) " ++
  "(resolve 3 2 0 1 0 (subst (0 (f 0))) (clause)) (final 3))"

def accepted (input proof : String) : Bool :=
  match decodeProblemWithSignature input, decodeCertificate proof with
  | .ok source, .ok certificate =>
    certificateWellFormed source certificate && check (preprocess source.problem) certificate
  | _, _ => false

def ensure (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"frontend test failed: {name}")

def parsesAs (source : String) (expected : Problem) : Bool :=
  match decodeProblem source with
  | .ok parsed => parsed == expected
  | .error _ => false

def failed : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

#eval ensure "documented refutation" (accepted exampleInput exampleProof)

#eval ensure "distinct variable names" (parsesAs "cnf(c,axiom,(p(X)|q(X0)|p(X)))." [[
    { positive := true, atom := { pred := 0, args := [.var 0] } },
    { positive := true, atom := { pred := 1, args := [.var 1] } },
    { positive := true, atom := { pred := 0, args := [.var 0] } }
  ]])

#eval ensure "nested first-occurrence symbol IDs" (parsesAs "cnf(c,axiom,(p(f(g(a)))))." [[
    { positive := true, atom := { pred := 0, args := [.app 0 [.app 1 [.app 2 []]]] } }
  ]])

#eval ensure "nested same-symbol arity" (parsesAs "cnf(c,axiom,(p(f(f(a)))))." [[
    { positive := true, atom := { pred := 0, args := [.app 0 [.app 0 [.app 1 []]]] } }
  ]])

#eval ensure "all ASCII whitespace" (parsesAs " \t\n\x0b\x0c\r" [])
#eval ensure "empty clause" (parsesAs "cnf(c,axiom,($false))." [[]])

def invalidInputs : List String := [
  "cnf(c,axiom,(p)).garbage", "cnfx(c,axiom,(p)).", "cnf(c,axiom,(p())).",
  "cnf(c,axiom,(p(a()))).", "cnf(c,axiom,(p)).cnf(c,axiom,(q)).",
  "cnf(c,axiom,(p(a)|p(a,a))).", "cnf(c,axiom,(p(f(a),f))).",
  "cnf(c,axiom,(p(f(f)))).", "cnf(c,axiom,(p(X)=p(a))).",
  "cnf(c,conjecture,(p)).", "cnf(c,axiom,(p),source).", "fof(c,axiom,(p)).",
  "include('file').", "cnf(c,axiom,($true)).", "cnf(c,axiom,($false|p)).",
  "cnf(c,axiom,(p(_))).", "cnf(c,axiom,(p(42))).", "% comment\n",
  "cnf(c,axiom,(p)).\uFEFF", "cnf(c,axiom,(p(é))).", "cnf(c,axiom,(p))",
  "cnf(c,axiom,(p(XY)|p(X Y)))."
]

#eval ensure "invalid source inputs" (invalidInputs.all (fun input => failed (decodeProblem input)))

def malformedCertificates : List String := [
  "(fang-proof 2 (input 0 0) (final 0))",
  "(fang-proof 1 (input 1 0) (final 1))",
  "(fang-proof 1 (input 0 0) (input 0 1) (final 0))",
  "(fang-proof 1 (input 0 0) (final 1))",
  "(fang-proof 1 (final 0))",
  "(fang-proof 1 (input 0 0) (final 0)) garbage",
  "(fang-proof 1 (input 0 0) (final 0) (input 1 0))",
  "(fang-proof 1 (input 0 0) (factor 1 1 0 1 (subst) (clause)) (final 1))",
  "(fang-proof 1 (input 0 0) (factor 1 0 0 0 (subst) (clause)) (final 1))",
  "(fang-proof 1 (input 0 0) (factor 1 0 0 1 (subst (0 (v 1)) (0 (v 2))) (clause)) (final 1))",
  "(fang-proof 1 (input 0 0) (wat 1 0) (final 1))"
]

#eval ensure "malformed certificates" (malformedCertificates.all (fun proof => failed (decodeCertificate proof)))

#eval ensure "nonempty final clause" (!accepted "cnf(c,axiom,(p(a)))."
  "(fang-proof 1 (input 0 0) (final 0))")

#eval ensure "input empty clause" (accepted "cnf(c,axiom,($false))."
  "(fang-proof 1 (input 0 0) (final 0))")

-- This certificate changes only the resolution binding, so its atoms no longer agree.
#eval ensure "altered binding" (!accepted exampleInput
  ("(fang-proof 1 (input 0 0) (input 1 1) " ++
   "(factor 2 0 0 1 (subst (1 (v 0))) (clause (pos 0 (v 0)))) " ++
   "(resolve 3 2 0 1 0 (subst) (clause)) (final 3))"))

end Fang.FrontendTests
