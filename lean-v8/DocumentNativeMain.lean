/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled TSTP export for a version-8 pair. It reads the same sealed files as
   the native checker, under the same limits, and prints the document of
   `exportDocument`, which rebuilds and rechecks the pair with the linear lexer.
   Exit codes: 0 document, 2 invalid file, 4 resource limit, 7 export error,
   64 usage, 74 I/O error. -/
import ExpandedDocument
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangDocumentNative

/-- Identical to the limits of the native version-8 checker. -/
def limits : FangOriginalReplay.Limits := {
  skolem := {
    core := {
      max_formula_depth := 64#usize, max_formula_nodes := 10000#usize,
      max_term_depth := 64#usize, max_input_term_nodes := 100000#usize,
      max_clauses := 1000#usize, max_literals_per_clause := 256#usize,
      max_literals := 100000#usize, max_stored_nodes := 1000000#usize,
      max_operations := 5000000#usize, max_binders := 10000#usize }
    max_declarations := 1000#usize, max_functions := 100000#usize,
    max_skolem_symbols := 10000#usize }
  removal := {
    max_formula_depth := 64#usize, max_operations := 5000000#usize,
    max_output_nodes := 1000000#usize }
  clausification := {
    max_formula_depth := 64#usize, max_formula_nodes := 10000#usize,
    max_term_depth := 64#usize, max_input_term_nodes := 100000#usize,
    max_clauses := 1000#usize, max_literals_per_clause := 256#usize,
    max_literals := 100000#usize, max_stored_nodes := 1000000#usize,
    max_operations := 5000000#usize } }

def maximumPredicates : Usize := 100000#usize
def maximumLiterals : Usize := 256#usize
def byteLimit : Nat := 1024 * 1024

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

def run (inputPath proofPath file : String) : IO UInt32 := do
  match ← readBytes inputPath "input" with
  | .error (code, message) => reject code message
  | .ok input =>
    match ← readText proofPath "certificate" with
    | .error (code, message) => reject code message
    | .ok proof =>
      match Fang.QuantifiedEqualityTstp.Expanded.exportDocument input.data.toList byteLimit proof limits
          maximumPredicates maximumLiterals file with
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
