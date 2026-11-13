/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The model certificate parser. Its result is data: the soundness theorems hold for whatever `FiniteModel` it
   returns, so this module carries no proofs. It requires one table for every function and predicate symbol of the
   statements and no other table, which keeps certificates exact and reports producer faults as certificate errors.

   Format, one item per line, tokens separated by single spaces, the text ending with a newline:
     fang-model 1
     domain N
     function NAME ARITY dense V ...            (N^ARITY values below N, row-major, first argument most significant)
     function NAME ARITY sparse DEFAULT K (A_1 ... A_ARITY V) ...
     predicate NAME ARITY dense B ...           (N^ARITY bits)
     predicate NAME ARITY sparse DEFAULT K (A_1 ... A_ARITY) ...   (the listed cells have the other bit)
     end
   NAME is the symbol name as the decoders store it, in lowercase hexadecimal of its ASCII bytes; a distinct object
   keeps its leading 0x00 byte. Numbers are decimal without leading zeros. -/
import ModelSemantics

namespace Fang.TptpCandidate.FullFof.Model

/-- Checker bounds. The theorems hold for every value. -/
structure Limits where
  maximumDomain : Nat
  maximumDenseCells : Nat
  maximumCells : Nat
  maximumWork : Nat

/-- `maximumWork` by the decision-9 rule: the largest step count of a sample check that finished within the case
    limits of 60 s and 2 GiB (341,204,423 steps, 17.8 s), plus 10%. -/
def defaultLimits : Limits where
  maximumDomain := 256
  maximumDenseCells := 1048576
  maximumCells := 1099511627776
  maximumWork := 375324866

inductive CertificateError where
  /-- Line (from 1) and what was expected there. -/
  | syntax : Nat → String → CertificateError
  /-- The domain is larger than the bound. -/
  | domain : Nat → CertificateError
  /-- The table on this line has more cells than the bound. -/
  | cells : Nat → CertificateError
  /-- A second table for one symbol, or a repeated cell of a sparse table, on this line. -/
  | duplicate : Nat → CertificateError
  /-- No table for this symbol (predicate or function, name, arity). -/
  | missing : Bool → String → Nat → CertificateError
  /-- The table on this line is for a symbol that does not occur. -/
  | unused : Nat → CertificateError
  deriving Repr

def CertificateError.isResource : CertificateError → Bool
  | .domain _ | .cells _ => true
  | _ => false

/-! Tokens. -/

def parseNumber (token : String) : Option Nat :=
  match token.toList with
  | [] => none
  | '0' :: _ :: _ => none
  | characters => characters.foldlM (fun total character =>
      if character.isDigit then some (total * 10 + (character.toNat - 48)) else none) 0

def hexDigit (character : Char) : Option Nat :=
  if 48 ≤ character.toNat ∧ character.toNat ≤ 57 then some (character.toNat - 48)
  else if 97 ≤ character.toNat ∧ character.toNat ≤ 102 then some (character.toNat - 87)
  else none

def decodeHex : List Char → String → Option String
  | [], output => some output
  | high :: low :: rest, output => do
    let first ← hexDigit high
    let second ← hexDigit low
    let code := first * 16 + second
    if code < 128 then decodeHex rest (output.push (Char.ofNat code)) else none
  | [_], _ => none

def parseName (token : String) : Option String :=
  if token.isEmpty then none else decodeHex token.toList ""

/-- `base ^ exponent` when it is at most `bound`. -/
def boundedPower (base bound : Nat) : Nat → Option Nat
  | 0 => if 1 ≤ bound then some 1 else none
  | exponent + 1 => do
    let smaller ← boundedPower base bound exponent
    if smaller * base ≤ bound then some (smaller * base) else none

/-! Tables. -/

def denseCells (line valueBound : Nat) : List String → Array Nat → Except CertificateError (Array Nat)
  | [], cells => .ok cells
  | token :: rest, cells =>
    match parseNumber token with
    | some value => if value < valueBound then denseCells line valueBound rest (cells.push value)
      else .error (.syntax line "value below the domain size")
    | none => .error (.syntax line "number")

def takeArguments (line base : Nat) : Nat → List String → Except CertificateError (List Nat × List String)
  | 0, rest => .ok ([], rest)
  | count + 1, token :: rest =>
    match parseNumber token with
    | some value =>
      if value < base then
        match takeArguments line base count rest with
        | .ok (more, final) => .ok (value :: more, final)
        | .error problem => .error problem
      else .error (.syntax line "argument below the domain size")
    | none => .error (.syntax line "number")
  | _ + 1, [] => .error (.syntax line "argument")

/-- `count` exceptions; a function exception carries its value, a predicate exception has the other bit. -/
def sparseCells (line base arity : Nat) (function : Bool) (fallback : Nat) :
    Nat → List String → Std.HashMap Nat Nat → Except CertificateError (Std.HashMap Nat Nat)
  | 0, [], cells => .ok cells
  | 0, _ :: _, _ => .error (.syntax line "end of line")
  | count + 1, tokens, cells =>
    match takeArguments line base arity tokens with
    | .error problem => .error problem
    | .ok (arguments, rest) =>
      let index := cellIndex base arguments
      if cells.contains index then .error (.duplicate line)
      else if function then
        match rest with
        | token :: rest =>
          match parseNumber token with
          | some value =>
            if value < base then sparseCells line base arity function fallback count rest (cells.insert index value)
            else .error (.syntax line "value below the domain size")
          | none => .error (.syntax line "number")
        | [] => .error (.syntax line "value")
      else sparseCells line base arity function fallback count rest (cells.insert index (1 - fallback))

structure TableLine where
  predicate : Bool
  key : String × Nat
  table : Table

def parseTable (limits : Limits) (base line : Nat) (tokens : List String) : Except CertificateError TableLine :=
  match tokens with
  | kind :: nameToken :: arityToken :: layout :: rest =>
    let predicate? : Option Bool := if kind == "function" then some false
      else if kind == "predicate" then some true else none
    match predicate?, parseName nameToken, parseNumber arityToken with
    | none, _, _ => .error (.syntax line "function or predicate")
    | _, none, _ => .error (.syntax line "hexadecimal name")
    | _, _, none => .error (.syntax line "arity")
    | some predicate, some name, some arity =>
      let valueBound := if predicate then 2 else base
      match boundedPower base limits.maximumCells arity with
      | none => .error (.cells line)
      | some cells =>
        if layout == "dense" then
          if cells ≤ limits.maximumDenseCells then
            if rest.length == cells then
              match denseCells line valueBound rest #[] with
              | .ok values => .ok ⟨predicate, (name, arity), .dense values⟩
              | .error problem => .error problem
            else .error (.syntax line "one value per cell")
          else .error (.cells line)
        else if layout == "sparse" then
          match rest with
          | fallbackToken :: countToken :: groups =>
            match parseNumber fallbackToken, parseNumber countToken with
            | some fallback, some count =>
              if fallback < valueBound then
                if count ≤ cells then
                  match sparseCells line base arity (!predicate) fallback count groups {} with
                  | .ok exceptions => .ok ⟨predicate, (name, arity), .sparse fallback exceptions⟩
                  | .error problem => .error problem
                else .error (.syntax line "at most one exception per cell")
              else .error (.syntax line "default below the domain size")
            | _, _ => .error (.syntax line "default and count")
          | _ => .error (.syntax line "default and count")
        else .error (.syntax line "dense or sparse")
  | _ => .error (.syntax line "table")

/-! The whole certificate. -/

structure Parsed where
  model : FiniteModel
  /-- Each table's kind, key and line, in certificate order. -/
  tables : List (Bool × (String × Nat) × Nat)

def words (line : String) : List String := line.splitOn " "

def addTables (limits : Limits) (base : Nat) : Nat → List String → Parsed → Except CertificateError Parsed
  | _, [], _ => .error (.syntax 0 "end")
  | line, [text], parsed =>
    if text == "end" then .ok parsed else .error (.syntax line "end")
  | line, text :: rest, parsed =>
    match parseTable limits base line (words text) with
    | .error problem => .error problem
    | .ok entry =>
      if entry.predicate then
        if parsed.model.predicates.contains entry.key then .error (.duplicate line)
        else addTables limits base (line + 1) rest
          ⟨{ parsed.model with predicates := parsed.model.predicates.insert entry.key entry.table },
            parsed.tables ++ [(true, entry.key, line)]⟩
      else
        if parsed.model.functions.contains entry.key then .error (.duplicate line)
        else addTables limits base (line + 1) rest
          ⟨{ parsed.model with functions := parsed.model.functions.insert entry.key entry.table },
            parsed.tables ++ [(false, entry.key, line)]⟩

def parseModel (limits : Limits) (text : String) : Except CertificateError Parsed :=
  match text.splitOn "\n" with
  | header :: domainLine :: rest =>
    if header != "fang-model 1" then .error (.syntax 1 "fang-model 1")
    else match rest.getLast?, words domainLine with
      | some "", ["domain", sizeToken] =>
        match parseNumber sizeToken with
        | some size =>
          if size = 0 then .error (.syntax 2 "a domain of at least one element")
          else if size > limits.maximumDomain then .error (.domain size)
          else addTables limits size 3 rest.dropLast ⟨⟨size - 1, {}, {}⟩, []⟩
        | none => .error (.syntax 2 "domain size")
      | some "", _ => .error (.syntax 2 "domain N")
      | _, _ => .error (.syntax 0 "a final newline")
  | _ => .error (.syntax 1 "fang-model 1")

/-- One table for every symbol of `statements`, and no other. -/
def coverage (statements : List Formula) (parsed : Parsed) : Except CertificateError Unit := do
  let functions := statements.flatMap Formula.functions
  let predicates := statements.flatMap Formula.predicates
  match functions.find? (fun symbol => !parsed.model.functions.contains symbol) with
  | some symbol => .error (.missing false symbol.1 symbol.2)
  | none => pure ()
  match predicates.find? (fun symbol => !parsed.model.predicates.contains symbol) with
  | some symbol => .error (.missing true symbol.1 symbol.2)
  | none => pure ()
  let functionSet : Std.HashSet (String × Nat) := Std.HashSet.ofList functions
  let predicateSet : Std.HashSet (String × Nat) := Std.HashSet.ofList predicates
  match parsed.tables.find? (fun (predicate, key, _) =>
      if predicate then !predicateSet.contains key else !functionSet.contains key) with
  | some (_, _, line) => .error (.unused line)
  | none => pure ()

def readCertificate (limits : Limits) (text : String) (statements : List Formula) :
    Except CertificateError FiniteModel := do
  let parsed ← parseModel limits text
  coverage statements parsed
  pure parsed.model

end Fang.TptpCandidate.FullFof.Model
