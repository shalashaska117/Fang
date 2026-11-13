/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Isolated compiled version-8 checker transport with naming: acceptsNamedD with
   the declaration limit, the formula height, the replay limits, the naming
   threshold and the table bounds of NativeLimits, whose acceptance proves the
   bytes unsatisfiable.
   The caller seals and hashes both files; each is read once. The input bytes are
   passed unchanged to the byte decoder; the certificate is preserved exactly as
   a Lean String. The input is read under `byteLimit` and the certificate under
   `certificateLimit`, both from NativeLimits. -/
import NamedDepthEntry
import NativeLimits
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangExpandedNamedNative
open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.FullFof.Integration.Named

inductive ReadError where
  | limit
  | invalidUtf8
  | nul : Nat → ReadError
  | nonAscii : Nat → ReadError
  | roundtrip

def byteLimit : Nat := Fang.NativeLimits.byteLimit

def certificateLimit : Nat := Fang.NativeLimits.certificateLimit

def readBytes (path : String) (limit : Nat := byteLimit) : IO (Except ReadError ByteArray) := do
  let bytes ← IO.FS.withFile path .read fun handle =>
    Fang.Runtime.readAtMost handle (limit + 1)
  if bytes.size > limit then return .error .limit
  return .ok bytes

def readText (path : String) (limit : Nat := certificateLimit) : IO (Except ReadError String) := do
  match ← readBytes path limit with
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

def namedMessage : NamedError → UInt32 × String
  | .replay error => replayMessage error
  | .slot => (4, "resource.replay.named-slot")
  | .range => (5, "replay.named-range")
  | .table => (4, "resource.replay.named-table")
  | .reservation error => bridgeMessage "replay.named-reservation" error
  | .reservationEffect => (5, "replay.named-reservation-runtime-effect")

/-- The record's naming threshold as the machine integer the replay takes. -/
def namingThreshold : Usize := { bv := BitVec.ofNat _ Fang.NativeLimits.namingThreshold }

def errorMessage : AcceptNamedError → UInt32 × String
  | .replay error => namedMessage error
  | .certificate (.certificate message) => parserMessage "certificate" 3 message
  | .certificate .signature => (6, "signature-rejection")
  | .certificate (.inference error) => (1, "logical-rejection: " ++ reprStr error)

def reject (outcome : UInt32 × String) : IO UInt32 := do
  (← IO.getStderr).putStrLn outcome.2
  return outcome.1

def run (inputPath proofPath : String) : IO UInt32 := do
  match ← readBytes inputPath with
  | .error error => reject (readMessage "input" error)
  | .ok input =>
    match ← readText proofPath with
    | .error error => reject (readMessage "certificate" error)
    | .ok proof =>
      match acceptsNamedD Fang.NativeLimits.declarationLimit Fang.NativeLimits.formulaDepthLimit
          input.data.toList byteLimit proof Fang.NativeLimits.replayLimits namingThreshold
          Fang.NativeLimits.maximumPredicates Fang.NativeLimits.maximumLiterals with
      | .error error => reject (errorMessage error)
      | .ok () =>
        IO.println "accepted-original-expanded-equality (native checker; compiler/runtime trusted)"
        return 0

end FangExpandedNamedNative

def main (args : List String) : IO UInt32 := do
  let [inputPath, proofPath] := args | do
    return ← FangExpandedNamedNative.reject (64, "usage: fang-expanded-native-named INPUT CERTIFICATE")
  try
    FangExpandedNamedNative.run inputPath proofPath
  catch error =>
    FangExpandedNamedNative.reject (74, "io-error: " ++ error.toString)
