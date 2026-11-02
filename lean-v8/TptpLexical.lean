/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent candidate lexer. No direct Rust or existing-certificate claim. -/
import Std

namespace Fang.TptpCandidate

inductive Kind where
  | lower : String → Kind
  | quoted : String → Kind
  | variable : String → Kind
  | integer : String → Kind
  | truth | falsity | implies
  | equality : Bool → Kind
  | punctuation : Char → Kind
  deriving Repr, BEq, DecidableEq

inductive Name where
  | atom : String → Name
  | integer : String → Name
  deriving Repr, BEq, DecidableEq

def Kind.name : Kind → Option Name
  | .lower value | .quoted value => some (.atom value)
  | .integer value => some (.integer value)
  | _ => none

inductive Space where
  | function | predicate
  deriving Repr, BEq, DecidableEq

structure SymbolKey where
  space : Space
  name : String
  arity : Nat
  deriving Repr, BEq, DecidableEq

structure Token where
  kind : Kind
  start : Nat
  stop : Nat
  raw : List Char
  deriving Repr, BEq, DecidableEq

inductive ErrorKind where
  | invalid | unsupported | resource | internal
  deriving Repr, BEq, DecidableEq

structure Error where
  kind : ErrorKind
  offset : Nat
  deriving Repr, BEq, DecidableEq

def lower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def upper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def word (c : Char) : Bool := lower c || upper c || digit c || c == '_'
def whitespace (c : Char) : Bool := c == ' ' || (9 ≤ c.toNat && c.toNat ≤ 13)
def commentChar (c : Char) : Bool := c.toNat ≤ 127 && c.toNat != 0

/-- After the opening quote; count includes the closing quote. -/
def quoted (origin offset : Nat) : List Char → Except Error (List Char × Nat)
  | [] => .error ⟨.invalid, origin⟩
  | '\'' :: _ => .ok ([], 1)
  | '\\' :: [] => .error ⟨.invalid, origin⟩
  | '\\' :: escaped :: rest =>
    if escaped == '\'' || escaped == '\\' then do
      let (value, count) ← quoted origin (offset + 2) rest
      pure (escaped :: value, count + 2)
    else .error ⟨.invalid, offset + 1⟩
  | c :: rest =>
    if 32 ≤ c.toNat && c.toNat ≤ 126 then do
      let (value, count) ← quoted origin (offset + 1) rest
      pure (c :: value, count + 1)
    else .error ⟨.invalid, offset⟩

def blockComment (origin offset : Nat) : List Char → Except Error Nat
  | [] => .error ⟨.invalid, origin⟩
  | '*' :: '/' :: _ => .ok 2
  | c :: rest =>
    if commentChar c then do
      pure ((← blockComment origin (offset + 1) rest) + 1)
    else .error ⟨.invalid, offset⟩

def integerValue (negative : Bool) (digits : List Char) : String :=
  String.ofList ((if negative && digits.head? != some '0' then ['-'] else []) ++ digits)

/-- Return a token or trivia and its exact consumed-byte count. -/
def piece (offset : Nat) : List Char → Except Error (Option Kind × Nat)
  | [] => .error ⟨.internal, offset⟩
  | c :: rest => do
    if whitespace c then return (none, 1)
    if c == '%' then
      let tail := rest.takeWhile (fun x => x != '\r' && x != '\n')
      if let some bad := tail.findIdx? (fun x => !commentChar x) then
        throw ⟨.invalid, offset + 1 + bad⟩
      return (none, tail.length + 1)
    if c == '/' && rest.head? == some '*' then
      return (none, (← blockComment offset (offset + 2) rest.tail) + 2)
    if c == '\'' then
      let (value, count) ← quoted offset (offset + 1) rest
      if value.isEmpty then throw ⟨.invalid, offset⟩
      return (some (.quoted (String.ofList value)), count + 1)
    if digit c || c == '+' || c == '-' then
      let signed := c == '+' || c == '-'
      let input := if signed then rest else c :: rest
      let digits := input.takeWhile digit
      if digits.isEmpty then throw ⟨.invalid, offset⟩
      if digits.head? == some '0' && digits.length != 1 then throw ⟨.invalid, offset⟩
      return (some (.integer (integerValue (c == '-') digits)),
        digits.length + if signed then 1 else 0)
    if lower c || upper c then
      let tail := rest.takeWhile word
      let value := String.ofList (c :: tail)
      return (some (if upper c then .variable value else .lower value), tail.length + 1)
    if c == '$' then
      let tail := rest.takeWhile word
      let value := String.ofList (c :: tail)
      if value == "$true" then return (some .truth, tail.length + 1)
      if value == "$false" then return (some .falsity, tail.length + 1)
      throw ⟨.unsupported, offset⟩
    if c == '=' && rest.head? == some '>' then return (some .implies, 2)
    if c == '=' then return (some (.equality true), 1)
    if c == '!' && rest.head? == some '=' then return (some (.equality false), 2)
    if c == '~' && (rest.head? == some '&' || rest.head? == some '|') then
      throw ⟨.unsupported, offset⟩
    if ['(', ')', ',', '.', '|', '~', '&', '!', '?', '[', ']', ':'].contains c then
      return (some (.punctuation c), 1)
    if ['>', '<', '"', '/', '_'].contains c then throw ⟨.unsupported, offset⟩
    throw ⟨.invalid, offset⟩

def lexLoop : Nat → List Char → Nat → Except Error (List Token)
  | 0, _, offset => .error ⟨.resource, offset⟩
  | _ + 1, [], _ => .ok []
  | fuel + 1, input@(_ :: _), offset => do
    let (kind, count) ← piece offset input
    if count == 0 || input.length < count then throw ⟨.internal, offset⟩
    let following ← lexLoop fuel (input.drop count) (offset + count)
    match kind with
    | none => pure following
    | some kind => pure (⟨kind, offset, offset + count, input.take count⟩ :: following)

/-- One character stands for one source byte; no UTF-8 replacement decoding. -/
def byteChars (input : List UInt8) : List Char := input.map (fun b => Char.ofNat b.toNat)

def tokenizeBytes (input : List UInt8) (maximumBytes : Nat := 1048576) :
    Except Error (List Token) :=
  if input.length > maximumBytes then .error ⟨.resource, 0⟩
  else lexLoop (input.length + 1) (byteChars input) 0

def tokenize (input : String) : Except Error (List Token) :=
  tokenizeBytes input.toUTF8.data.toList

end Fang.TptpCandidate
