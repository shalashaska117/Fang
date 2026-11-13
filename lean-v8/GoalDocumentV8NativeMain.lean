/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled TSTP export for one conjecture of a signed single-file pair. It reads
   the input under the record's byte limit and the certificate under its
   certificate limit, the limits of the checker that accepted the pair, and
   prints the document of `exportGoalDocument` for the goal index, which
   rebuilds and rechecks the pair under the limits record. Exit codes:
   0 document, 2 invalid file, 4 resource limit, 7 export error, 64 usage,
   74 I/O error. -/
import GoalDocumentV8
import NativeLimits
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangGoalDocumentNative

def byteLimit : Nat := Fang.NativeLimits.byteLimit
def usage : String := "usage: fang-goal-tstp INPUT CERTIFICATE GOAL FILE-NAME"

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
      match Fang.TptpCandidate.GoalDocumentV8.exportGoalDocument input.data.toList byteLimit goal proof file with
      | .error message => reject (if message.startsWith "resource-exhaustion" then 4 else 7) message
      | .ok text =>
        IO.print text
        return 0

end FangGoalDocumentNative

def main (args : List String) : IO UInt32 := do
  let [inputPath, proofPath, goalText, file] := args | do
    return ← FangGoalDocumentNative.reject 64 FangGoalDocumentNative.usage
  let some goal := FangGoalDocumentNative.parseGoal goalText | do
    return ← FangGoalDocumentNative.reject 64 FangGoalDocumentNative.usage
  try
    FangGoalDocumentNative.run inputPath proofPath goal file
  catch error =>
    FangGoalDocumentNative.reject 74 ("io-error: " ++ error.toString)
