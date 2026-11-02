/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Isolated compiled checker for signed role tasks over a sealed include bundle, with the role-aware framer over framer revision 2 and the counted declaration limit of the limits record: at most `Fang.NativeLimits.declarationLimit` formulas per file, with duplicate names found through a hash set. The framer runs the linear framer lexer, the reversed statement splitter and the counted record decoder, and `V3.limited_eq` proves it equal to the list framer the meanings are stated over. The caller seals and hashes every file; each is read once. The orchestrating command selects the task: `--goal N` for the selected conjecture with index N in expansion order, or `--inputs` for a bundle without a selected conjecture. `--goals` lists the selected conjectures with their items and reads no certificate. Bundle files come as ROOT PATH FILE triples, top-level file first, as in bundle-v8/native. The replay limits, the predicate and literal caps and the per-file byte limit are those of NativeLimits.lean; the message functions are those of the earlier signed checker main SignedBundleNativeMainFast. -/
import RoleReplayLimit
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangSignedBundleNativeLimit
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

def bundleMessage : V2.TaskError → UInt32 × String
  | .read error => readErrorMessage error
  | .noGoal => (2, "task.no-such-goal")
  | .cnfGoal => (5, "task.cnf-goal")
  | .goalsPresent => (2, "task.goals-present")
  | .replay error => signedMessage error

def errorMessage : V2.AcceptError → UInt32 × String
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

def check (task : Task) (files : List (Fang.TptpCandidate.FullFof.Coverage.Key × List UInt8)) (proof : String) :
    Except V2.AcceptError String :=
  match task with
  | .goal index => do
    let item ← V3.acceptsGoal V3.limited files byteLimit index proof limits maximumPredicates maximumLiterals
    pure s!"accepted-goal {index} item {item.1} {item.2} (native checker; compiler/runtime trusted)"
  | .inputs => do
    V3.acceptsInputs V3.limited files byteLimit proof limits maximumPredicates maximumLiterals
    pure "accepted-inputs-unsatisfiable (native checker; compiler/runtime trusted)"
  | .goals => pure ""

/-- The selected conjectures of the decoded bundle with their items, so that an orchestrating command takes the goal count from the checker's own decoding. -/
def goals (files : List (Fang.TptpCandidate.FullFof.Coverage.Key × List UInt8)) : Except V2.ReadError String := do
  let read ← V3.readBundle V3.limited files byteLimit
  let items := goalItems read.bundle read.items
  pure (s!"goals {items.length}
" ++ String.join (items.zipIdx.map fun (pair, index) =>
    s!"goal {index} item {pair.1.1} {pair.1.2}
"))

def run (task : Task) (proofPath : String) (fileArguments : List String) : IO UInt32 := do
  if let .goals := task then
    match ← readFiles fileArguments 0 with
    | .error outcome => return ← reject outcome
    | .ok files =>
      match goals files with
      | .error error => return ← reject (readErrorMessage error)
      | .ok text =>
        IO.print text
        return 0
  match ← readText proofPath with
  | .error error => reject (readMessage "certificate" error)
  | .ok proof =>
    match ← readFiles fileArguments 0 with
    | .error outcome => reject outcome
    | .ok files =>
      match check task files proof with
      | .error error => reject (errorMessage error)
      | .ok line =>
        IO.println line
        return 0

def usage : UInt32 × String :=
  (64, "usage: fang-signed-bundle-native-limit (--goal N CERTIFICATE | --inputs CERTIFICATE | --goals) ROOT PATH FILE [ROOT PATH FILE]...")

end FangSignedBundleNativeLimit

def main (args : List String) : IO UInt32 := do
  let parsed : Option (FangSignedBundleNativeLimit.Task × String × List String) := match args with
    | "--goal" :: index :: proofPath :: rest => index.toNat?.map fun value => (.goal value, proofPath, rest)
    | "--inputs" :: proofPath :: rest => some (.inputs, proofPath, rest)
    | "--goals" :: rest => some (.goals, "", rest)
    | _ => none
  let some (task, proofPath, fileArguments@(_ :: _)) := parsed |
    FangSignedBundleNativeLimit.reject FangSignedBundleNativeLimit.usage
  try
    FangSignedBundleNativeLimit.run task proofPath fileArguments
  catch error =>
    FangSignedBundleNativeLimit.reject (74, "io-error: " ++ error.toString)
