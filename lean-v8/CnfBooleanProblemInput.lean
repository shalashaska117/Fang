/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import CnfBooleanDeclarationSound
import FofScope

namespace Fang.TptpCandidate.FullFof.CnfBoolean

def declarations : Nat → List Name → Nat → List Token → Except Error (List Declaration)
  | 0, _, endOffset, tokens => failure .resource endOffset tokens
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, tokens@(_ :: _) => do
    if seen.length ≥ 1000 then failure .resource endOffset tokens
    let (first, rest) ← declaration seen endOffset tokens
    let tail ← declarations fuel (first.name :: seen) endOffset rest
    pure (first :: tail)

def decodeBytes (input : List UInt8) (maximumBytes : Nat := 1048576) : Except Error (List Declaration) := do
  let tokens ← tokenizeBytes input maximumBytes
  declarations (tokens.length + 1) [] input.length tokens

def decode (input : String) : Except Error (List Declaration) :=
  decodeBytes input.toUTF8.data.toList


end Fang.TptpCandidate.FullFof.CnfBoolean
