/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import TptpLexical

namespace Fang.TptpCandidate.FullFof

inductive Kind where
  | legacy : TptpCandidate.Kind → Kind
  | reverse | nand | nor | iff | xor
  deriving Repr, BEq, DecidableEq

structure Token where
  kind : Kind
  start : Nat
  stop : Nat
  raw : List Char
  deriving Repr, BEq, DecidableEq

/-- All name, numeric-name, comment and old punctuation rules are the frozen
    lexer. Only five contiguous binary operators have added cases. -/
def piece (offset : Nat) (input : List Char) : Except Error (Option Kind × Nat) :=
  match input with
  | '<' :: '=' :: '>' :: _ => .ok (some .iff, 3)
  | '<' :: '~' :: '>' :: _ => .ok (some .xor, 3)
  | '<' :: '=' :: _ => .ok (some .reverse, 2)
  | '~' :: '&' :: _ => .ok (some .nand, 2)
  | '~' :: '|' :: _ => .ok (some .nor, 2)
  | _ => do
    let (kind, count) ← TptpCandidate.piece offset input
    pure (kind.map Kind.legacy, count)

def lexLoop : Nat → List Char → Nat → Except Error (List Token)
  | 0, _, offset => .error ⟨.resource, offset⟩
  | _ + 1, [], _ => .ok []
  | fuel + 1, input@(_ :: _), offset => do
    let (kind, count) ← piece offset input
    if count == 0 || input.length < count then throw ⟨.internal, offset⟩
    let tail ← lexLoop fuel (input.drop count) (offset + count)
    match kind with
    | none => pure tail
    | some kind => pure (⟨kind, offset, offset + count, input.take count⟩ :: tail)

def tokenizeBytes (input : List UInt8) (maximumBytes : Nat := 1048576) :
    Except Error (List Token) :=
  if input.length > maximumBytes then .error ⟨.resource, 0⟩
  else lexLoop (input.length + 1) (byteChars input) 0

def tokenize (input : String) : Except Error (List Token) :=
  tokenizeBytes input.toUTF8.data.toList

end Fang.TptpCandidate.FullFof
