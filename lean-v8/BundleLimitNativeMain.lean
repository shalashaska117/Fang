/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled version-8 checker for a sealed bundle on the limits record. `BundleFastNativeMain.lean` with the hashed framer `BundleLimit.limited` in place of the linear framer and the limits of `NativeLimits.lean`: at most `Fang.NativeLimits.declarationLimit` formulas per file, duplicate names found through a hash set, and the replay limits, the predicate and literal caps and the per-file byte limit of that record. `BundleLimit.acceptsBundleLimited_refuted` states what an acceptance proves. The binary keeps the name `fang-bundle-native-fast`; the readers and error messages are those of `BundleFastNativeMain.lean`. -/
import BundleReplayLimit
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangBundleLimitNative
open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.BundleV8

def limits : FangOriginalReplay.Limits := Fang.NativeLimits.replayLimits
def maximumPredicates : Usize := Fang.NativeLimits.maximumPredicates
def maximumLiterals : Usize := Fang.NativeLimits.maximumLiterals
def byteLimit : Nat := Fang.NativeLimits.byteLimit

inductive ReadError where
  | limit
  | invalidUtf8
  | nul : Nat → ReadError
  | nonAscii : Nat → ReadError
  | roundtrip

def readBytes (path : String) : IO (Except ReadError ByteArray) := do
  let bytes ← IO.FS.withFile path .read fun handle =>
    Fang.Runtime.readAtMost handle (byteLimit + 1)
  if bytes.size > byteLimit then return .error .limit
  return .ok bytes

def readText (path : String) : IO (Except ReadError String) := do
  match ← readBytes path with
  | .error error => return .error error
  | .ok bytes =>
    let some text := String.fromUTF8? bytes | return .error .invalidUtf8
    if let some offset := bytes.data.findIdx? (fun byte => byte == 0) then
      return .error (.nul offset)
    if let some offset := bytes.data.findIdx? (fun byte => byte.toNat > 127) then
      return .error (.nonAscii offset)
    if text.toUTF8 != bytes then return .error .roundtrip
    return .ok text

def readMessage (label : String) : ReadError → UInt32 × String
  | .limit => (4, s!"resource.bytes.{label}")
  | .invalidUtf8 => (2, s!"invalid-utf8.{label}")
  | .nul offset => (2, s!"invalid-nul.{label}:{offset}")
  | .nonAscii offset => (2, s!"unsupported-non-ascii.{label}:{offset}")
  | .roundtrip => (5, s!"internal-byte-roundtrip.{label}")

def parserMessage (label : String) (otherwise : UInt32) (message : String) : UInt32 × String :=
  (if message.startsWith "resource-exhaustion" then 4 else otherwise, label ++ ": " ++ message)

def frontendMessage (error : Fang.TptpCandidate.Error) : UInt32 × String :=
  match error.kind with
  | .invalid => (2, s!"replay.input.invalid:{error.offset}")
  | .unsupported => (2, s!"replay.input.unsupported:{error.offset}")
  | .resource => (4, s!"resource.replay.input:{error.offset}")
  | .internal => (5, s!"replay.input.internal:{error.offset}")

def bridgeMessage (label : String) : fang_fof_equality_bridge.Error → UInt32 × String
  | .PredicateLimit => (4, label ++ ".predicate-limit")
  | .SymbolId => (4, label ++ ".symbol-width")
  | .UnknownPredicate => (2, label ++ ".unknown-predicate")
  | .PredicateArity => (2, label ++ ".predicate-arity")
  | .ReservedArity => (2, label ++ ".reserved-arity")
  | .LiteralLimit => (4, label ++ ".literal-limit")

def originalInputMessage : FangOriginalInput.Error → UInt32 × String
  | .width error => (4, "resource.replay.width: " ++ reprStr error)
  | .missingFunctionArity => (2, "replay.missing-function-arity")
  | .missingPredicateArity => (2, "replay.missing-predicate-arity")

def transportMessage : FangQuantifiedEqualityInput.Error → UInt32 × String
  | .input message => parserMessage "replay.transport-input" 2 message
  | .transport error => originalInputMessage error
  | .reservation error => bridgeMessage "replay.reservation" error
  | .runtimeEffect => (5, "replay.transport-runtime-effect")
  | .divergence => (5, "replay.transport-divergence")

def preprocessingMessage : FangOriginalReplay.Error → UInt32 × String
  | .input message => parserMessage "replay.preprocessing-input" 2 message
  | .encoding error => originalInputMessage error
  | .skolem (.Resource _) => (4, "resource.replay.skolem")
  | .skolem (.Core (.Resource _)) => (4, "resource.replay.skolem-core")
  | .skolem (.Core (.Invalid _)) => (2, "replay.skolem-invalid")
  | .skolem (.Core (.Unsupported _)) => (2, "replay.skolem-unsupported")
  | .removal (.Resource _) => (4, "resource.replay.removal")
  | .removal (.ResidualExistential _) => (2, "replay.residual-existential")
  | .clausification (.Resource _) => (4, "resource.replay.clausification")
  | .clausification (.Invalid _) => (2, "replay.clausification-invalid")
  | .runtimeEffect => (5, "replay.runtime-effect")
  | .divergence => (5, "replay.divergence")
  | .clauseBlockCount => (5, "replay.clause-block-count")

def conversionMessage : FangQuantifiedEqualityReplay.Conversion.Error → UInt32 × String
  | .encoding error => (4, "resource.replay.conversion-width: " ++ reprStr error)
  | .observation error => transportMessage error
  | .conversion error => bridgeMessage "replay.conversion" error

def replayMessage : ReplayError → UInt32 × String
  | .input error => frontendMessage error
  | .nonliteral => (2, "replay.nonliteral")
  | .transport error => transportMessage error
  | .preprocessing error => preprocessingMessage error
  | .conversion error => conversionMessage error

def errorMessage : AcceptError → UInt32 × String
  | .replay error => replayMessage error
  | .certificate (.certificate message) => parserMessage "certificate" 3 message
  | .certificate .signature => (6, "signature-rejection")
  | .certificate (.inference error) => (1, "logical-rejection: " ++ reprStr error)

def bundleMessage : BundleError → UInt32 × String
  | .frame error => match error.kind with
    | .invalid => (2, s!"bundle.frame.invalid:{error.offset}")
    | .unsupported => (2, s!"bundle.frame.unsupported:{error.offset}")
    | .resource => (4, s!"resource.bundle.frame:{error.offset}")
    | .internal => (5, s!"bundle.frame.internal:{error.offset}")
  | .shape => (2, "bundle.shape")
  | .expand .missing => (2, "bundle.include.missing")
  | .expand .cycle => (2, "bundle.include.cycle")
  | .expand .selectionMissing => (2, "bundle.selection.missing")
  | .expand .selectionAmbiguous => (2, "bundle.selection.ambiguous")
  | .expand .fuel => (4, "resource.bundle.include-depth")
  | .nonliteral => (2, "bundle.nonliteral")

def bundleErrorMessage : BundleAcceptError → UInt32 × String
  | .replay (.bundle error) => bundleMessage error
  | .replay (.replay error) => replayMessage error
  | .certificate (.certificate message) => parserMessage "certificate" 3 message
  | .certificate .signature => (6, "signature-rejection")
  | .certificate (.inference error) => (1, "logical-rejection: " ++ reprStr error)

def reject (outcome : UInt32 × String) : IO UInt32 := do
  (← IO.getStderr).putStrLn outcome.2
  return outcome.1

/-- Total bytes over all bundle files. -/
def bundleLimit : Nat := 4 * byteLimit

def parseRoot : String → Option Root
  | "base" => some .base
  | "tptp" => some .tptp
  | _ => none

/-- Arguments after the certificate: ROOT PATH FILE triples, top-level first. -/
def readFiles : List String → Nat → IO (Except (UInt32 × String) (List (Key × List UInt8)))
  | [], _ => return .ok []
  | rootText :: pathText :: filePath :: rest, total => do
    let some root := parseRoot rootText | return .error (64, "usage: unknown root " ++ rootText)
    let path := pathText.splitOn "/"
    match ← readBytes filePath with
    | .error error => return .error (readMessage ("bundle-file " ++ pathText) error)
    | .ok bytes =>
      if total + bytes.size > bundleLimit then return .error (4, "resource.bytes.bundle")
      match ← readFiles rest (total + bytes.size) with
      | .error outcome => return .error outcome
      | .ok others => return .ok ((⟨root, path⟩, bytes.data.toList) :: others)
  | _, _ => return .error (64, "usage: bundle files come as ROOT PATH FILE triples")

def run (proofPath : String) (fileArguments : List String) : IO UInt32 := do
  match ← readText proofPath with
  | .error error => reject (readMessage "certificate" error)
  | .ok proof =>
    match ← readFiles fileArguments 0 with
    | .error outcome => reject outcome
    | .ok files =>
      match BundleLimit.acceptsBundle BundleLimit.limited files byteLimit proof limits maximumPredicates maximumLiterals with
      | .error error => reject (bundleErrorMessage error)
      | .ok () =>
        IO.println "accepted-original-bundle-equality (native checker; compiler/runtime trusted)"
        return 0

end FangBundleLimitNative

def main (args : List String) : IO UInt32 := do
  let proofPath :: fileArguments@(_ :: _) := args | do
    return ← FangBundleLimitNative.reject (64, "usage: fang-bundle-native-fast CERTIFICATE ROOT PATH FILE [ROOT PATH FILE]...")
  try
    FangBundleLimitNative.run proofPath fileArguments
  catch error =>
    FangBundleLimitNative.reject (74, "io-error: " ++ error.toString)
