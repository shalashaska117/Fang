/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Native adapter for depth-parametric named role replay and premise lines.
   The entry receives formula depth, naming threshold and certificate bytes
   from the final shared record; this module fixes none of those values. -/
import NamedCitedDepth
import PremiseLine
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangSignedBundleNativeV6
open Fang.TptpCandidate.FullFof.Integration
open Fang.TptpCandidate.Roles.Signed
open Fang.TptpCandidate.Roles.Bundle
open Fang.TptpCandidate.Roles.Bundle.V2

def limits : FangOriginalReplay.Limits := Fang.NativeLimits.replayLimits
def maximumPredicates : Usize := Fang.NativeLimits.maximumPredicates
def maximumLiterals : Usize := Fang.NativeLimits.maximumLiterals
def byteLimit : Nat := Fang.NativeLimits.byteLimit

/-- Total bytes over all bundle files. -/
def bundleLimit : Nat := 4 * byteLimit

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

def readText (maximum : Nat) (path : String) : IO (Except ReadError String) := do
  let bytes ← IO.FS.withFile path .read fun handle => Fang.Runtime.readAtMost handle (maximum + 1)
  if bytes.size > maximum then return .error .limit
  else
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

def signedMessage : SignedError → UInt32 × String
  | .input error => frontendMessage error
  | .nonliteral => (2, "replay.nonliteral")
  | .noGoal => (2, "task.no-such-goal")
  | .cnfGoal => (5, "task.cnf-goal")
  | .goalsPresent => (2, "task.goals-present")
  | .transport error => transportMessage error
  | .width error => originalInputMessage error
  | .preprocessing error => preprocessingMessage error
  | .conversion error => conversionMessage error

def namedMessage : Fang.TptpCandidate.FullFof.Integration.Named.NamedError → UInt32 × String
  | .replay (.input error) => frontendMessage error
  | .replay .nonliteral => (2, "replay.nonliteral")
  | .replay (.transport error) => transportMessage error
  | .replay (.preprocessing error) => preprocessingMessage error
  | .replay (.conversion error) => conversionMessage error
  | .slot => (4, "resource.replay.naming-slot")
  | .range => (2, "replay.naming-range")
  | .table => (4, "resource.replay.naming-table")
  | .reservation error => bridgeMessage "replay.naming-reservation" error
  | .reservationEffect => (5, "replay.naming-reservation-effect")

def signedNamedMessage : SignedNamedError → UInt32 × String
  | .signed error => signedMessage error
  | .named error => namedMessage error

def readErrorMessage : V2.ReadError → UInt32 × String
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
  | .modes => (2, "bundle.mixed-goal-modes")
  | .nonliteral => (2, "replay.nonliteral")

def bundleMessage : V3.Depth.Named.TaskError → UInt32 × String
  | .read error => readErrorMessage error
  | .noGoal => (2, "task.no-such-goal")
  | .cnfGoal => (5, "task.cnf-goal")
  | .goalsPresent => (2, "task.goals-present")
  | .replay error => signedNamedMessage error

def errorMessage : V3.Depth.Named.AcceptError → UInt32 × String
  | .task error => bundleMessage error
  | .certificate (.certificate message) => parserMessage "certificate" 3 message
  | .certificate .signature => (6, "signature-rejection")
  | .certificate (.inference error) => (1, "logical-rejection: " ++ reprStr error)

def reject (outcome : UInt32 × String) : IO UInt32 := do
  (← IO.getStderr).putStrLn outcome.2
  return outcome.1

def parseRoot : String → Option Fang.TptpCandidate.FullFof.Coverage.Root
  | "base" => some .base
  | "tptp" => some .tptp
  | _ => none

/-- Arguments after the certificate: ROOT PATH FILE triples, top-level first. -/
def readFiles : List String → Nat →
    IO (Except (UInt32 × String) (List (Fang.TptpCandidate.FullFof.Coverage.Key × List UInt8)))
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

inductive Task where
  | goal : Nat → Task
  | inputs
  | goals

/-- The premise line split off by `PremiseLine.split`, with the certificate after it as a string. -/
def splitPremises (proof : String) :
    Option (Except Unit (List Fang.TptpCandidate.FullFof.Coverage.Item × String)) :=
  (PremiseLine.split proof).map fun result => result.bind fun (cited, rest) =>
    if cited.Nodup then .ok (cited, String.ofList rest) else .error ()

def citedMessage : V3.Depth.Named.CitedAcceptError → UInt32 × String
  | .task (.task error) => bundleMessage error
  | .task (.citation item) => (3, s!"certificate.premises.citation:{item.1}:{item.2}")
  | .certificate error => errorMessage (.certificate error)

def check (maxDepth threshold : Nat) (task : Task) (files : List (Fang.TptpCandidate.FullFof.Coverage.Key × List UInt8)) (proof : String) :
    Except (UInt32 × String) String :=
  match task, splitPremises proof with
  | .goals, _ => pure ""
  | _, some (.error ()) => .error (3, "certificate.premises")
  | .goal index, none =>
    match V3.Depth.Named.acceptsGoal (V3.Depth.frameBundleHashed Fang.NativeLimits.declarationLimit maxDepth) files byteLimit index proof limits { bv := BitVec.ofNat _ threshold } maximumPredicates maximumLiterals with
    | .ok item => pure s!"accepted-goal {index} item {item.1} {item.2} (native checker; compiler/runtime trusted)"
    | .error error => .error (errorMessage error)
  | .goal index, some (.ok (cited, rest)) =>
    match V3.Depth.Named.acceptsGoalCited (V3.Depth.frameBundleHashed Fang.NativeLimits.declarationLimit maxDepth) files byteLimit index cited rest limits { bv := BitVec.ofNat _ threshold } maximumPredicates maximumLiterals with
    | .ok item => pure s!"accepted-goal {index} item {item.1} {item.2} (native checker; compiler/runtime trusted)"
    | .error error => .error (citedMessage error)
  | .inputs, none =>
    match V3.Depth.Named.acceptsInputs (V3.Depth.frameBundleHashed Fang.NativeLimits.declarationLimit maxDepth) files byteLimit proof limits { bv := BitVec.ofNat _ threshold } maximumPredicates maximumLiterals with
    | .ok () => pure "accepted-inputs-unsatisfiable (native checker; compiler/runtime trusted)"
    | .error error => .error (errorMessage error)
  | .inputs, some (.ok (cited, rest)) =>
    match V3.Depth.Named.acceptsInputsCited (V3.Depth.frameBundleHashed Fang.NativeLimits.declarationLimit maxDepth) files byteLimit cited rest limits { bv := BitVec.ofNat _ threshold } maximumPredicates maximumLiterals with
    | .ok () => pure "accepted-inputs-unsatisfiable (native checker; compiler/runtime trusted)"
    | .error error => .error (citedMessage error)

/-- The selected conjectures of the decoded bundle with their items, so that an orchestrating command takes the goal count from the checker's own decoding. -/
def goals (maxDepth : Nat) (files : List (Fang.TptpCandidate.FullFof.Coverage.Key × List UInt8)) : Except V2.ReadError String := do
  let read ← V3.readBundle (V3.Depth.frameBundleHashed Fang.NativeLimits.declarationLimit maxDepth) files byteLimit
  let items := goalItems read.bundle read.items
  pure (s!"goals {items.length}
" ++ String.join (items.zipIdx.map fun (pair, index) =>
    s!"goal {index} item {pair.1.1} {pair.1.2}
"))

def run (maxDepth threshold certificateBytes : Nat) (task : Task) (proofPath : String) (fileArguments : List String) : IO UInt32 := do
  if let .goals := task then
    match ← readFiles fileArguments 0 with
    | .error outcome => return ← reject outcome
    | .ok files =>
      match goals maxDepth files with
      | .error error => return ← reject (readErrorMessage error)
      | .ok text =>
        IO.print text
        return 0
  match ← readText certificateBytes proofPath with
  | .error error => reject (readMessage "certificate" error)
  | .ok proof =>
    match ← readFiles fileArguments 0 with
    | .error outcome => reject outcome
    | .ok files =>
      match check maxDepth threshold task files proof with
      | .error outcome => reject outcome
      | .ok line =>
        IO.println line
        return 0

def usage : UInt32 × String :=
  (64, "usage: fang-signed-bundle-native-v6 (--goal N CERTIFICATE | --inputs CERTIFICATE | --goals) ROOT PATH FILE [ROOT PATH FILE]...")

end FangSignedBundleNativeV6

def mainWithLimits (maxDepth threshold certificateBytes : Nat) (args : List String) : IO UInt32 := do
  let parsed : Option (FangSignedBundleNativeV6.Task × String × List String) := match args with
    | "--goal" :: index :: proofPath :: rest => index.toNat?.map fun value => (.goal value, proofPath, rest)
    | "--inputs" :: proofPath :: rest => some (.inputs, proofPath, rest)
    | "--goals" :: rest => some (.goals, "", rest)
    | _ => none
  let some (task, proofPath, fileArguments@(_ :: _)) := parsed |
    FangSignedBundleNativeV6.reject FangSignedBundleNativeV6.usage
  try
    FangSignedBundleNativeV6.run maxDepth threshold certificateBytes task proofPath fileArguments
  catch error =>
    FangSignedBundleNativeV6.reject (74, "io-error: " ++ error.toString)
