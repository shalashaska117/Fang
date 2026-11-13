/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled TSTP export for one conjecture of a signed single-file pair, or with
   `--inputs` for the inputs task of a signed single file without a conjecture. It reads
   the input under the record's byte limit and the certificate under its
   certificate limit, the limits of the checker that accepted the pair, and
   prints the document of the named `exportGoalDocument` for the goal index,
   which rebuilds and rechecks the pair with naming under the limits record: the
   declaration limit, the formula height, the replay limits, the naming
   threshold and the table bounds. With `--inputs` it prints the document of
   `exportInputsDocument`, which rebuilds and rechecks the inputs task the same
   way; a file with a conjecture is an export error. Exit codes:
   0 document, 2 invalid file, 4 resource limit, 7 export error, 64 usage,
   74 I/O error. -/
import NamedGoalDocumentDepth
import NamedInputsDocument
import NativeLimits
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangGoalDocumentNative

def byteLimit : Nat := Fang.NativeLimits.byteLimit

/-- The record's naming threshold as the machine integer the replay takes. -/
def namingThreshold : Usize := { bv := BitVec.ofNat _ Fang.NativeLimits.namingThreshold }
def usage : String :=
  "usage: fang-goal-tstp-named INPUT CERTIFICATE GOAL FILE-NAME | --inputs INPUT CERTIFICATE FILE-NAME"

def reject (code : UInt32) (message : String) : IO UInt32 := do
  (← IO.getStderr).putStrLn message
  return code

def readBytes (path label : String) (limit : Nat) : IO (Except (UInt32 × String) ByteArray) := do
  let bytes ← IO.FS.withFile path .read fun handle =>
    Fang.Runtime.readAtMost handle (limit + 1)
  if bytes.size > limit then return .error (4, s!"resource.bytes.{label}")
  return .ok bytes

def readText (path label : String) (limit : Nat) : IO (Except (UInt32 × String) String) := do
  match ← readBytes path label limit with
  | .error error => return .error error
  | .ok bytes =>
    let some text := String.fromUTF8? bytes | return .error (2, s!"invalid-utf8.{label}")
    if bytes.data.any (fun byte => byte == 0 || byte.toNat > 127) then
      return .error (2, s!"unsupported-byte.{label}")
    return .ok text

/-- A goal index is decimal digits without a sign or leading zeros. -/
def parseGoal (text : String) : Option Nat :=
  if text.isEmpty || !text.all Char.isDigit || (text.length > 1 && text.front == '0') then none
  else text.toNat?

def run (inputPath proofPath : String) (goal : Nat) (file : String) : IO UInt32 := do
  match ← readBytes inputPath "input" byteLimit with
  | .error (code, message) => reject code message
  | .ok input =>
    match ← readText proofPath "certificate" Fang.NativeLimits.certificateLimit with
    | .error (code, message) => reject code message
    | .ok proof =>
      match Fang.TptpCandidate.GoalDocument.NamedDepth.exportGoalDocument Fang.NativeLimits.declarationLimit
          Fang.NativeLimits.formulaDepthLimit input.data.toList byteLimit goal proof Fang.NativeLimits.replayLimits
          namingThreshold Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals file with
      | .error message => reject (if message.startsWith "resource-exhaustion" then 4 else 7) message
      | .ok text =>
        IO.print text
        return 0

def runInputs (inputPath proofPath : String) (file : String) : IO UInt32 := do
  match ← readBytes inputPath "input" byteLimit with
  | .error (code, message) => reject code message
  | .ok input =>
    match ← readText proofPath "certificate" Fang.NativeLimits.certificateLimit with
    | .error (code, message) => reject code message
    | .ok proof =>
      match Fang.TptpCandidate.InputsDocument.NamedDepth.exportInputsDocument Fang.NativeLimits.declarationLimit
          Fang.NativeLimits.formulaDepthLimit input.data.toList byteLimit proof Fang.NativeLimits.replayLimits
          namingThreshold Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals file with
      | .error message => reject (if message.startsWith "resource-exhaustion" then 4 else 7) message
      | .ok text =>
        IO.print text
        return 0

end FangGoalDocumentNative

def main (args : List String) : IO UInt32 := do
  if let ["--inputs", inputPath, proofPath, file] := args then
    try
      return ← FangGoalDocumentNative.runInputs inputPath proofPath file
    catch error =>
      return ← FangGoalDocumentNative.reject 74 ("io-error: " ++ error.toString)
  let [inputPath, proofPath, goalText, file] := args | do
    return ← FangGoalDocumentNative.reject 64 FangGoalDocumentNative.usage
  let some goal := FangGoalDocumentNative.parseGoal goalText | do
    return ← FangGoalDocumentNative.reject 64 FangGoalDocumentNative.usage
  try
    FangGoalDocumentNative.run inputPath proofPath goal file
  catch error =>
    FangGoalDocumentNative.reject 74 ("io-error: " ++ error.toString)
