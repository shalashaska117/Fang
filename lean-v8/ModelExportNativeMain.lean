/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled finite model document exporter, `fang-model-tstp`. It takes the arguments of `fang-model-check`
   (`ModelNativeMain.lean`), reads them under the same limits, runs the same entry, and prints the document of
   `ModelExport.lean` for the accepted model, with the layout `defaultLayout`. `ModelExport.lean` states what a printed
   document is. Exit codes: 0 document; 1 to 5 the model checker's own codes when it does not accept; 4 also when the
   document exceeds a bound; 7 export error; 64 usage; 74 I/O error. A model the checker accepts keeps its status when
   no document is printed. -/
import ModelExport
import NativeLimits
import Fang.BoundedInput

namespace FangModelExportNative
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

def failureMessage (inputLabel : String) : ExportFailure → UInt32 × String
  | .check error => errorMessage inputLabel error
  | .document message => (if message.startsWith "resource" then 4 else 7, message)

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

def exportFiles (task : Task) (files : List (Coverage.Key × List UInt8)) (certificate : String) :
    Except (UInt32 × String) String :=
  let outcome : Except ExportFailure String := match task with
    | .single => .error (.document "usage: --single takes one input file")
    | .bundle => exportBundle defaultLimits defaultLayout files byteLimit certificate
    | .inputs => exportInputs defaultLimits defaultLayout files byteLimit certificate
    | .goal index => exportGoal defaultLimits defaultLayout files byteLimit index certificate
  match task, outcome with
  | .single, _ => .error (64, "usage: --single takes one input file")
  | _, .ok text => .ok text
  | _, .error problem => .error (failureMessage "bundle.frame" problem)

def run (task : Task) (certificatePath : String) (arguments : List String) : IO UInt32 := do
  match ← readText certificatePath with
  | .error error => reject (readMessage "certificate" error)
  | .ok certificate =>
    match task, arguments with
    | .single, [inputPath] =>
      match ← readBytes inputPath with
      | .error error => reject (readMessage "input" error)
      | .ok input =>
        match exportSingle defaultLimits defaultLayout Fang.NativeLimits.declarationLimit input.data.toList byteLimit
            certificate with
        | .ok text =>
          IO.print text
          return 0
        | .error problem => reject (failureMessage "input" problem)
    | .single, _ => reject (64, "usage: --single takes one input file")
    | _, _ =>
      match ← readFiles arguments 0 with
      | .error outcome => reject outcome
      | .ok files =>
        match exportFiles task files certificate with
        | .ok text =>
          IO.print text
          return 0
        | .error outcome => reject outcome

def usage : UInt32 × String :=
  (64, "usage: fang-model-tstp (--single CERTIFICATE INPUT | (--bundle | --inputs | --goal N) CERTIFICATE ROOT PATH FILE [ROOT PATH FILE]...)")

end FangModelExportNative

def main (args : List String) : IO UInt32 := do
  let parsed : Option (FangModelExportNative.Task × String × List String) := match args with
    | "--single" :: certificate :: rest => some (.single, certificate, rest)
    | "--bundle" :: certificate :: rest => some (.bundle, certificate, rest)
    | "--inputs" :: certificate :: rest => some (.inputs, certificate, rest)
    | "--goal" :: index :: certificate :: rest => index.toNat?.map fun value => (.goal value, certificate, rest)
    | _ => none
  let some (task, certificate, arguments@(_ :: _)) := parsed | FangModelExportNative.reject FangModelExportNative.usage
  try
    FangModelExportNative.run task certificate arguments
  catch error =>
    FangModelExportNative.reject (74, "io-error: " ++ error.toString)
