/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled model checker. `--single` decodes one input file with the counted decoder of the single-file checker;
   `--bundle` frames a sealed bundle with `BundleLimit.limited`; `--inputs` and `--goal N` frame it with the role frame
   `V3.limited`, and N is the index the signed checker's `--goals` listing prints. Bundle files come as ROOT PATH FILE
   triples, top-level file first. The declaration limit and the byte limits are those of `NativeLimits.lean`, the
   model bounds those of `Model.defaultLimits`. The caller seals and hashes every file; each is read once. Acceptance
   prints one line and exits 0; `ModelEntries.lean` states what each acceptance proves. -/
import ModelEntries
import NativeLimits
import Fang.BoundedInput

namespace FangModelNative
open Fang.TptpCandidate.FullFof
open Fang.TptpCandidate.FullFof.Model

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

def inputMessage (label : String) (error : Fang.TptpCandidate.Error) : UInt32 × String :=
  match error.kind with
  | .invalid => (2, s!"{label}.invalid:{error.offset}")
  | .unsupported => (2, s!"{label}.unsupported:{error.offset}")
  | .resource => (4, s!"resource.{label}:{error.offset}")
  | .internal => (5, s!"{label}.internal:{error.offset}")

def hexName (label : String) : String :=
  String.join (label.toList.map fun character =>
    let code := character.toNat
    let digit (value : Nat) : Char := if value < 10 then Char.ofNat (48 + value) else Char.ofNat (87 + value)
    String.singleton (digit (code / 16)) ++ String.singleton (digit (code % 16)))

def certificateMessage : CertificateError → UInt32 × String
  | .syntax line what => (3, s!"certificate: invalid-syntax at line {line}: expected {what}")
  | .domain size => (4, s!"resource.model.domain: {size}")
  | .cells line => (4, s!"resource.model.cells: line {line}")
  | .duplicate line => (3, s!"certificate: duplicate at line {line}")
  | .missing predicate label arity =>
    let kind := if predicate then "predicate" else "function"
    (3, s!"certificate: missing {kind} {hexName label} {arity}")
  | .unused line => (3, s!"certificate: unused table at line {line}")

def errorMessage (inputLabel : String) : ModelError → UInt32 × String
  | .input error => inputMessage inputLabel error
  | .expand .missing => (2, "bundle.include.missing")
  | .expand .cycle => (2, "bundle.include.cycle")
  | .expand .selectionMissing => (2, "bundle.selection.missing")
  | .expand .selectionAmbiguous => (2, "bundle.selection.ambiguous")
  | .expand .fuel => (4, "resource.bundle.include-depth")
  | .shape => (2, "bundle.shape")
  | .modes => (2, "bundle.mixed-goal-modes")
  | .noGoal => (2, "task.no-such-goal")
  | .goalsPresent => (2, "task.goals-present")
  | .certificate error => certificateMessage error
  | .work => (4, "resource.model.evaluation")
  | .rejected (.statement index) => (1, s!"model-rejection: statement {index}")
  | .rejected (.scope index) => (5, s!"model.internal-scope: statement {index}")
  | .goalHolds => (1, "model-rejection: goal-holds")
  | .goalScope => (5, "model.internal-scope: goal")
  | .objects => (1, "model-rejection: objects")

def reject (outcome : UInt32 × String) : IO UInt32 := do
  (← IO.getStderr).putStrLn outcome.2
  return outcome.1

def parseRoot : String → Option Coverage.Root
  | "base" => some .base
  | "tptp" => some .tptp
  | _ => none

/-- ROOT PATH FILE triples, top-level first. -/
def readFiles : List String → Nat → IO (Except (UInt32 × String) (List (Coverage.Key × List UInt8)))
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
  | single
  | bundle
  | inputs
  | goal : Nat → Task

def trusted : String := " (native checker; compiler/runtime trusted)"

def checkFiles (task : Task) (files : List (Coverage.Key × List UInt8)) (certificate : String) :
    Except (UInt32 × String) String :=
  match task with
  | .single => .error (64, "usage: --single takes one input file")
  | .bundle =>
    match acceptsBundle defaultLimits Coverage.BundleLimit.limited files byteLimit certificate with
    | .ok () => .ok ("accepted-model-bundle" ++ trusted)
    | .error error => .error (errorMessage "bundle.frame" error)
  | .inputs =>
    match acceptsInputs defaultLimits Fang.TptpCandidate.Roles.Bundle.V3.limited files byteLimit certificate with
    | .ok () => .ok ("accepted-model-inputs" ++ trusted)
    | .error error => .error (errorMessage "bundle.frame" error)
  | .goal index =>
    match acceptsGoal defaultLimits Fang.TptpCandidate.Roles.Bundle.V3.limited files byteLimit index certificate with
    | .ok item => .ok (s!"accepted-countermodel-goal {index} item {item.1} {item.2}" ++ trusted)
    | .error error => .error (errorMessage "bundle.frame" error)

def run (task : Task) (certificatePath : String) (arguments : List String) : IO UInt32 := do
  match ← readText certificatePath with
  | .error error => reject (readMessage "certificate" error)
  | .ok certificate =>
    match task, arguments with
    | .single, [inputPath] =>
      match ← readBytes inputPath with
      | .error error => reject (readMessage "input" error)
      | .ok input =>
        match acceptsSingle defaultLimits Fang.NativeLimits.declarationLimit input.data.toList byteLimit certificate with
        | .ok () =>
          IO.println ("accepted-model-single" ++ trusted)
          return 0
        | .error error => reject (errorMessage "input" error)
    | .single, _ => reject (64, "usage: --single takes one input file")
    | _, _ =>
      match ← readFiles arguments 0 with
      | .error outcome => reject outcome
      | .ok files =>
        match checkFiles task files certificate with
        | .ok line =>
          IO.println line
          return 0
        | .error outcome => reject outcome

def usage : UInt32 × String :=
  (64, "usage: fang-model-check (--single CERTIFICATE INPUT | (--bundle | --inputs | --goal N) CERTIFICATE ROOT PATH FILE [ROOT PATH FILE]...)")

end FangModelNative

def main (args : List String) : IO UInt32 := do
  let parsed : Option (FangModelNative.Task × String × List String) := match args with
    | "--single" :: certificate :: rest => some (.single, certificate, rest)
    | "--bundle" :: certificate :: rest => some (.bundle, certificate, rest)
    | "--inputs" :: certificate :: rest => some (.inputs, certificate, rest)
    | "--goal" :: index :: certificate :: rest => index.toNat?.map fun value => (.goal value, certificate, rest)
    | _ => none
  let some (task, certificate, arguments@(_ :: _)) := parsed | FangModelNative.reject FangModelNative.usage
  try
    FangModelNative.run task certificate arguments
  catch error =>
    FangModelNative.reject (74, "io-error: " ++ error.toString)
