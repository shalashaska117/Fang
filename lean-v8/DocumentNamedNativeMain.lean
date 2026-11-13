/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled TSTP export for a version-8 pair. It reads the same sealed files as
   the native checker, the input under the record's byte limit and the
   certificate under its certificate limit, and prints the document of the
   named `exportDocumentD`, which rebuilds and rechecks the pair with naming
   through the limited decoder at the record's declaration limit and formula
   height, under the record's replay limits, naming threshold and table bounds.
   Exit codes: 0 document, 2 invalid file, 4 resource limit, 7 export error,
   64 usage, 74 I/O error. -/
import NamedDocumentDepth
import NativeLimits
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangDocumentNamedNative

def byteLimit : Nat := Fang.NativeLimits.byteLimit

/-- The record's naming threshold as the machine integer the replay takes. -/
def namingThreshold : Usize := { bv := BitVec.ofNat _ Fang.NativeLimits.namingThreshold }

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
      match Fang.QuantifiedEqualityTstp.NamedExport.exportDocumentD Fang.NativeLimits.declarationLimit
          Fang.NativeLimits.formulaDepthLimit input.data.toList byteLimit proof Fang.NativeLimits.replayLimits
          namingThreshold Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals file with
      | .error message => reject (if message.startsWith "resource-exhaustion" then 4 else 7) message
      | .ok text =>
        IO.print text
        return 0

end FangDocumentNamedNative

def main (args : List String) : IO UInt32 := do
  let [inputPath, proofPath, file] := args | do
    return ← FangDocumentNamedNative.reject 64 "usage: fang-v8-tstp-named INPUT CERTIFICATE FILE-NAME"
  try
    FangDocumentNamedNative.run inputPath proofPath file
  catch error =>
    FangDocumentNamedNative.reject 74 ("io-error: " ++ error.toString)
