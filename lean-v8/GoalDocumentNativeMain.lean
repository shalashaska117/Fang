/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compiled TSTP export for one conjecture of a signed single-file pair. It reads
   the input and the certificate under the limits of the single-file exporter
   and prints the document of `exportGoalDocument` for the goal index, which
   rebuilds and rechecks the pair. Exit codes: 0 document, 2 invalid file,
   4 resource limit, 7 export error, 64 usage, 74 I/O error. -/
import GoalDocument
import Fang.BoundedInput

open Aeneas Aeneas.Std

namespace FangGoalDocumentNative

/-- The limits of the single-file exporter (`DocumentNativeMain`), on the 1,000-declaration path. -/
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
def usage : String := "usage: fang-goal-tstp INPUT CERTIFICATE GOAL FILE-NAME"

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

/-- A goal index is decimal digits without a sign or leading zeros. -/
def parseGoal (text : String) : Option Nat :=
  if text.isEmpty || !text.all Char.isDigit || (text.length > 1 && text.front == '0') then none
  else text.toNat?

def run (inputPath proofPath : String) (goal : Nat) (file : String) : IO UInt32 := do
  match ← readBytes inputPath "input" with
  | .error (code, message) => reject code message
  | .ok input =>
    match ← readText proofPath "certificate" with
    | .error (code, message) => reject code message
    | .ok proof =>
      match Fang.TptpCandidate.GoalDocument.exportGoalDocument input.data.toList byteLimit goal proof limits
          maximumPredicates maximumLiterals file with
      | .error message => reject (if message.startsWith "resource-exhaustion" then 4 else 7) message
      | .ok text =>
        IO.print text
        return 0

end FangGoalDocumentNative

def main (args : List String) : IO UInt32 := do
  let [inputPath, proofPath, goalText, file] := args | do
    return ← FangGoalDocumentNative.reject 64 FangGoalDocumentNative.usage
  let some goal := FangGoalDocumentNative.parseGoal goalText | do
    return ← FangGoalDocumentNative.reject 64 FangGoalDocumentNative.usage
  try
    FangGoalDocumentNative.run inputPath proofPath goal file
  catch error =>
    FangGoalDocumentNative.reject 74 ("io-error: " ++ error.toString)
