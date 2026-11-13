/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent signed CNF constants over the frozen term/FOF parser. -/
import ExpandedFofInput

namespace Fang.TptpCandidate.FullFof.CnfBoolean

def IsAtomic : Formula → Prop
  | .atom _ _ | .equal _ _ | .truth | .falsity => True
  | _ => False

def negate (endOffset : Nat) (tokens : List Token) : Formula → Except Error Formula
  | value@(.atom _ _) | value@(.equal _ _) | value@(.truth) | value@(.falsity) =>
      .ok (.neg value)
  | _ => failure .invalid endOffset tokens

def atomic (endOffset : Nat) (tokens : List Token) : Except Error (Formula × List Token) :=
  match tokens with
  | token :: rest =>
    match token.kind with
    | .legacy .truth => .ok (.truth, rest)
    | .legacy .falsity => .ok (.falsity, rest)
    | _ => atom (2 * tokens.length + 1) none endOffset tokens
  | [] => failure .invalid endOffset tokens

def wrappedAtom (endOffset : Nat) (tokens : List Token) : Except Error (Formula × List Token) := do
  if isChar '(' tokens then
    let (value, rest) ← atomic endOffset tokens.tail
    let (_, final) ← expect ')' endOffset rest
    pure (value, final)
  else atomic endOffset tokens

def literal (endOffset : Nat) (tokens : List Token) : Except Error (Formula × List Token) := do
  let negative := isChar '~' tokens
  let body := if negative then tokens.tail else tokens
  if isChar '!' body || isChar '?' body then failure .unsupported endOffset body
  if negative then
    let (value, rest) ← wrappedAtom endOffset body
    let value ← negate endOffset body value
    pure (value, rest)
  else atomic endOffset body

def disjunction : Nat → Nat → List Token → Except Error (List Formula × List Token)
  | 0, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, endOffset, tokens => do
    let (first, rest) ← literal endOffset tokens
    if isChar '|' rest then
      let (tail, final) ← disjunction fuel endOffset rest.tail
      pure (first :: tail, final)
    else if rest.head?.map Token.kind == some (.legacy .implies) || isChar '&' rest then
      failure .unsupported endOffset rest
    else pure ([first], rest)

def clause : Nat → Nat → Nat → List Token → Except Error (List Formula × List Token)
  | 0, _, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, endOffset, tokens => do
    if depth > 64 then failure .resource endOffset tokens
    if isChar '(' tokens then
      let (values, rest) ← clause fuel (depth + 1) endOffset tokens.tail
      let (_, final) ← expect ')' endOffset rest
      pure (values, final)
    else disjunction (tokens.length + 1) endOffset tokens

end Fang.TptpCandidate.FullFof.CnfBoolean
