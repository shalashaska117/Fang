import Fang.CertificateInput

/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.

Named compiled regressions for the P0 case index. These #eval checks are not
per-instance kernel proofs. The general decoder/checker proofs are separate.
The exact ASCII inputs and certificates are embedded below.
-/

namespace Fang.P0NamedRegressions

def identifiers : String := "cnf(clause_0,axiom,(p_name(Xlower_0,f_name(a_0),Xlower_1,Xlower_0)))."
def variableAndConstant : String := "cnf(c,axiom,(p(Xlower,xlower)))."
def emptyInput : String := ""
def tffInput : String := "tff(c,axiom,(p(a)))."
def thfInput : String := "thf(c,axiom,(p(a)))."
def universalInput : String := "cnf(c,axiom,(![X]:p(X)))."
def existentialInput : String := "cnf(c,axiom,(?[X]:p(X)))."
def disequalityInput : String := "cnf(c,axiom,(a!=b))."
def doubleQuotedInput : String := "cnf(c,axiom,(p(\"a\")))."
def rawBackslashInput : String := "cnf(c,axiom,(p(a\\b)))."
def literalEscapeInput : String := "cnf(c,axiom,(p(a\\n)))."
def escapedApostropheInput : String := "cnf(c,axiom,(p('a\\'b')))."
def escapedDoubleQuoteInput : String := "cnf(c,axiom,(p(a\\\"b)))."
def unitInput : String := "cnf(c,axiom,(p(a)))."
def unitSamePositionForgery : String := "(fang-proof 1 (input 0 0) (factor 1 0 0 0 (subst) (clause)) (final 1))"
def unitInputOnly : String := "(fang-proof 1 (input 0 0) (final 0))"
def validInput : String := "cnf(c0,axiom,(p(a))).cnf(c1,axiom,(~p(a)))."
def validProof : String := "(fang-proof 1 (input 0 0) (input 1 1) (resolve 2 0 0 1 0 (subst) (clause)) (final 2))"

private def ensure (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"P0 named regression failed: {name}")
  IO.println s!"P0 named regression passed: {name}"

private def parsedAs (source : String) (problem : Problem)
    (functions predicates : List Nat) : Bool :=
  match decodeProblemWithSignature source with
  | .ok actual => actual.problem == problem && actual.functionArities == functions &&
      actual.predicateArities == predicates
  | .error _ => false

private def exactError (result : Except String α) (expected : String) : Bool :=
  match result with
  | .error actual => actual == expected
  | .ok _ => false

private def accepted (input proof : String) : Bool :=
  match decodeProblemWithSignature input, decodeCertificate proof with
  | .ok source, .ok certificate =>
    certificateWellFormed source certificate && check (preprocess source.problem) certificate
  | _, _ => false

#eval ensure "underscores and lowercase letters in variable identifiers"
  (parsedAs identifiers [[⟨true, ⟨0, [.var 0, .app 0 [.app 1 []], .var 1, .var 0]⟩⟩]] [1, 0] [4])

#eval ensure "initial letter distinguishes variable from constant"
  (parsedAs variableAndConstant [[⟨true, ⟨0, [.var 0, .app 0 []]⟩⟩]] [0] [2])

#eval ensure "exact empty source" (parsedAs emptyInput [] [] [])

#eval ensure "TFF unsupported at declaration start"
  (exactError (decodeProblem tffInput) "unsupported: only cnf declarations are supported at byte 0")
#eval ensure "THF unsupported at declaration start"
  (exactError (decodeProblem thfInput) "unsupported: only cnf declarations are supported at byte 0")
#eval ensure "universal quantifier unsupported at byte 13"
  (exactError (decodeProblem universalInput) "unsupported at byte 13: character !")
#eval ensure "existential quantifier unsupported at byte 13"
  (exactError (decodeProblem existentialInput) "unsupported at byte 13: character ?")
#eval ensure "disequality unsupported at byte 14"
  (exactError (decodeProblem disequalityInput) "unsupported at byte 14: character !")
#eval ensure "double-quoted constant unsupported at byte 15"
  (exactError (decodeProblem doubleQuotedInput) "unsupported at byte 15: character \"")
#eval ensure "raw backslash invalid at byte 16"
  (exactError (decodeProblem rawBackslashInput) "invalid-syntax at byte 16: unexpected character \\")
#eval ensure "literal backslash-n is not whitespace"
  (exactError (decodeProblem literalEscapeInput) "invalid-syntax at byte 16: unexpected character \\")
#eval ensure "escaped apostrophe does not enable quoted identifiers"
  (exactError (decodeProblem escapedApostropheInput) "unsupported at byte 15: character '")
#eval ensure "escaped double quote invalid at the backslash"
  (exactError (decodeProblem escapedDoubleQuoteInput) "invalid-syntax at byte 16: unexpected character \\")

#eval ensure "unit-clause wire forgery rejects equal factoring positions"
  (exactError (decodeCertificate unitSamePositionForgery)
    "invalid-certificate: factoring positions must differ at byte 42")
#eval ensure "unit-clause wire forgery cannot certify the source"
  (!accepted unitInput unitSamePositionForgery)

-- A valid non-refuting wire certificate decodes successfully but cannot close p(a).
#eval ensure "unit input-only certificate is decoded and well formed"
  (match decodeProblemWithSignature unitInput, decodeCertificate unitInputOnly with
   | .ok source, .ok certificate => certificateWellFormed source certificate
   | _, _ => false)
#eval ensure "unit input-only certificate is not a refutation" (!accepted unitInput unitInputOnly)
#eval ensure "ground resolution wire positive control" (accepted validInput validProof)

end Fang.P0NamedRegressions
