/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled TSTP export for a sealed bundle pair on the limits record. `BundleTstpNativeMain.lean` with the hashed framer `BundleLimit.limited` and the limits of `NativeLimits.lean`, as in the bundle checker `fang-bundle-native-fast` of `BundleLimitNativeMain.lean`: it takes the same arguments, reads them under the same limits, and prints the document of `BundleLimit.exportBundleDocument` for that frame, which rebuilds and rechecks the pair. The binary keeps the name `fang-bundle-tstp`; the readers and exit codes are those of `BundleTstpNativeMain.lean`: 0 document, 2 invalid file, 4 resource limit, 7 export error, 64 usage, 74 I/O error. -/
import BundleDocumentLimit
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangBundleTstpLimitNative

open Fang.TptpCandidate.FullFof.Coverage (Key Root)

/-- The limits of the native bundle checker. -/
def limits : FangOriginalReplay.Limits := Fang.NativeLimits.replayLimits
def maximumPredicates : Usize := Fang.NativeLimits.maximumPredicates
def maximumLiterals : Usize := Fang.NativeLimits.maximumLiterals
def byteLimit : Nat := Fang.NativeLimits.byteLimit

/-- Total bytes over all bundle files, as in the bundle checker. -/
def bundleLimit : Nat := 4 * byteLimit

def reject (code : UInt32) (message : String) : IO UInt32 := do
  (← IO.getStderr).putStrLn message
  return code

def readBytes (path label : String) : IO (Except (UInt32 × String) ByteArray) := do
  let bytes ← IO.FS.withFile path .read fun handle =>
    Fang.Runtime.readAtMost handle (byteLimit + 1)
  if bytes.size > byteLimit then return .error (4, s!"resource.bytes.{label}")
  return .ok bytes

def readText (path label : String) : IO (Except (UInt32 × String) String) := do
  match ← readBytes path label with
  | .error error => return .error error
  | .ok bytes =>
    let some text := String.fromUTF8? bytes | return .error (2, s!"invalid-utf8.{label}")
    if bytes.data.any (fun byte => byte == 0 || byte.toNat > 127) then
      return .error (2, s!"unsupported-byte.{label}")
    return .ok text

def parseRoot : String → Option Root
  | "base" => some .base
  | "tptp" => some .tptp
  | _ => none

/-- Arguments after the certificate: ROOT PATH FILE triples, top-level first. -/
def readFiles : List String → Nat → IO (Except (UInt32 × String) (List (Key × List UInt8)))
  | [], _ => return .ok []
  | rootText :: pathText :: filePath :: rest, total => do
    let some root := parseRoot rootText | return .error (64, "usage: unknown root " ++ rootText)
    match ← readBytes filePath ("bundle-file " ++ pathText) with
    | .error outcome => return .error outcome
    | .ok bytes =>
      if total + bytes.size > bundleLimit then return .error (4, "resource.bytes.bundle")
      match ← readFiles rest (total + bytes.size) with
      | .error outcome => return .error outcome
      | .ok others => return .ok ((⟨root, pathText.splitOn "/"⟩, bytes.data.toList) :: others)
  | _, _ => return .error (64, "usage: bundle files come as ROOT PATH FILE triples")

def run (proofPath : String) (fileArguments : List String) : IO UInt32 := do
  match ← readText proofPath "certificate" with
  | .error (code, message) => reject code message
  | .ok proof =>
    match ← readFiles fileArguments 0 with
    | .error (code, message) => reject code message
    | .ok files =>
      match Fang.QuantifiedEqualityTstp.Expanded.BundleLimit.exportBundleDocument
          Fang.TptpCandidate.FullFof.Coverage.BundleLimit.limited files byteLimit proof limits
          maximumPredicates maximumLiterals with
      | .error message => reject (if message.startsWith "resource-exhaustion" then 4 else 7) message
      | .ok text =>
        IO.print text
        return 0

end FangBundleTstpLimitNative

def main (args : List String) : IO UInt32 := do
  let proofPath :: fileArguments@(_ :: _) := args | do
    return ← FangBundleTstpLimitNative.reject 64 "usage: fang-bundle-tstp CERTIFICATE ROOT PATH FILE [ROOT PATH FILE]..."
  try
    FangBundleTstpLimitNative.run proofPath fileArguments
  catch error =>
    FangBundleTstpLimitNative.reject 74 ("io-error: " ++ error.toString)
