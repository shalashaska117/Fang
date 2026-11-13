/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled TSTP export for a version-8 pair. It reads the same sealed files as
   the native checker, the input under the record's byte limit and the
   certificate under its certificate limit, and prints the document of
   `exportDocument`, which rebuilds and rechecks the pair with the linear lexer
   under the record's replay limits.
   Exit codes: 0 document, 2 invalid file, 4 resource limit, 7 export error,
   64 usage, 74 I/O error. -/
import ExpandedDocument
import NativeLimits
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangDocumentNative

def byteLimit : Nat := Fang.NativeLimits.byteLimit

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

def run (inputPath proofPath file : String) : IO UInt32 := do
  match ← readBytes inputPath "input" byteLimit with
  | .error (code, message) => reject code message
  | .ok input =>
    match ← readText proofPath "certificate" Fang.NativeLimits.certificateLimit with
    | .error (code, message) => reject code message
    | .ok proof =>
      match Fang.QuantifiedEqualityTstp.Expanded.exportDocument input.data.toList byteLimit proof
          Fang.NativeLimits.replayLimits Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals
          file with
      | .error message => reject (if message.startsWith "resource-exhaustion" then 4 else 7) message
      | .ok text =>
        IO.print text
        return 0

end FangDocumentNative

def main (args : List String) : IO UInt32 := do
  let [inputPath, proofPath, file] := args | do
    return ← FangDocumentNative.reject 64 "usage: fang-v8-tstp INPUT CERTIFICATE FILE-NAME"
  try
    FangDocumentNative.run inputPath proofPath file
  catch error =>
    FangDocumentNative.reject 74 ("io-error: " ++ error.toString)
