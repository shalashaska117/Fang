/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent certificate-input decoder. No production command imports it.
   Decoder-to-grammar and semantic encoding obligations are still open. -/
import QuantifiedProblem
import Fang.Input

namespace Fang.QuantifiedFrontend
open Frontend

def lexAux : Nat → List Char → Nat → Except String (List Token)
  | 0, _, offset => .error s!"resource-exhaustion at byte {offset}: lexer fuel"
  | _ + 1, [], _ => .ok []
  | fuel + 1, c :: cs, offset => do
    if asciiSpace c then lexAux fuel cs (offset + 1)
    else if wordChar c then
      let (tail, rest) := cs.span wordChar
      let chars := c :: tail
      let remaining ← lexAux fuel rest (offset + chars.length)
      pure ({ text := String.ofList chars, offset } :: remaining)
    else if c == '=' && cs.head? == some '>' then
      let remaining ← lexAux fuel cs.tail (offset + 2)
      pure ({ text := "=>", offset } :: remaining)
    else if c == '~' && (cs.head? == some '&' || cs.head? == some '|') then
      .error s!"unsupported at byte {offset}: NAND/NOR"
    else if ['(', ')', ',', '.', '|', '~', '&', '!', '?', '[', ']', ':'].contains c then
      let remaining ← lexAux fuel cs (offset + 1)
      pure ({ text := String.singleton c, offset } :: remaining)
    else if ['=', '>', '<', '\'', '"', '%', '/'].contains c then
      .error s!"unsupported at byte {offset}: token outside the quantified fragment"
    else .error s!"invalid-syntax at byte {offset}: character"

def tokenize (input : String) : Except String (List Token) := do
  if input.toList.any (fun c => c.toNat > 127) then
    .error "invalid-syntax: input must contain ASCII bytes only"
  else lexAux (input.toList.length + 1) input.toList 0

mutual
def termWithin (bound : List Nat) : Term → Bool
  | .var id => bound.contains id
  | .app _ args => termsWithin bound args

def termsWithin (bound : List Nat) : List Term → Bool
  | [] => true
  | term :: rest => termWithin bound term && termsWithin bound rest
end

def formulaWithin (bound : List Nat) : QuantifiedFOF.Formula → Bool
  | .atom atom => termsWithin bound atom.args
  | .truth | .falsity => true
  | .neg body => formulaWithin bound body
  | .conj left right | .disj left right | .implies left right =>
      formulaWithin bound left && formulaWithin bound right
  | .all id body | .ex id body => formulaWithin (id :: bound) body

/-- Allocate names before the body. Repeated names reuse their source ID; each
    occurrence still creates a binder node. Rectification is a later step. -/
def binders : Nat → Parser (List Nat)
  | 0 => fail "resource-exhaustion: binder decoder fuel"
  | fuel + 1 => do
    let offset ← position
    let name ← consume
    if !variableName name then failAt offset "invalid-syntax: expected a variable binder"
    let id ← variableId name
    let delimiter ← peek
    if delimiter == some "]" then
      expect "]"
      pure [id]
    else if delimiter == some "," then
      expect ","
      pure (id :: (← binders fuel))
    else if delimiter == some ":" then fail "unsupported: typed binders"
    else fail "invalid-syntax: expected comma or closing bracket"

def bindFormula (universal : Bool) (names : List Nat) (body : QuantifiedFOF.Formula) : QuantifiedFOF.Formula :=
  names.foldr (fun name tail => if universal then .all name tail else .ex name tail) body

def formula : Nat → Parser QuantifiedFOF.Formula
  | 0 => fail "resource-exhaustion: formula decoder fuel"
  | fuel + 1 => do
    let next ← peek
    if next == some "$true" then expect "$true"; pure .truth
    else if next == some "$false" then expect "$false"; pure .falsity
    else if next == some "~" then
      expect "~"
      pure (.neg (← formula fuel))
    else if next == some "!" || next == some "?" then
      discard consume
      expect "["
      let names ← binders fuel
      expect ":"
      pure (bindFormula (next == some "!") names (← formula fuel))
    else if next == some "(" then
      expect "("
      let left ← formula fuel
      let operator ← peek
      if operator == some "&" || operator == some "|" || operator == some "=>" then
        discard consume
        let right ← formula fuel
        expect ")"
        if operator == some "&" then pure (.conj left right)
        else if operator == some "|" then pure (.disj left right)
        else pure (.implies left right)
      else
        expect ")"
        pure left
    else
      match next with
      | some name =>
        if variableName name then fail "invalid-syntax: expected a predicate"
        else if lowerName name then
          let atom ← literal fuel
          pure (.atom atom.atom)
        else fail "unsupported: expected an uninterpreted formula"
      | none => fail "invalid-syntax: expected a formula"

def statement (fuel : Nat) : Parser NamedQuantified.NumericDeclaration := do
  if (← peek) == some "cnf" then
    pure (.cnf (← Frontend.statement fuel))
  else if (← peek) == some "fof" then
    expect "fof"
    expect "("
    let offset ← position
    let name ← consume
    if !lowerName name then failAt offset "invalid-syntax: statement name must be a lower-case identifier"
    let state ← get
    if state.clauseNames.contains name then failAt offset "invalid-syntax: duplicate statement name"
    set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
    expect ","
    if (← peek) != some "axiom" then fail "unsupported: only the axiom role is supported"
    expect "axiom"
    expect ","
    let body ← formula fuel
    if !formulaWithin [] body then fail "invalid-syntax: free FOF variable"
    if (← peek) == some "," then fail "unsupported: TPTP annotations"
    expect ")"
    expect "."
    pure (.fof body)
  else
    let kind ← peek
    if kind == some "tff" || kind == some "thf" || kind == some "tcf" || kind == some "include" then
      fail "unsupported: only CNF and FOF statements are supported"
    else fail "invalid-syntax: expected CNF or FOF statement"

def statements : Nat → Parser (List NamedQuantified.NumericDeclaration)
  | 0 => fail "resource-exhaustion: declaration decoder fuel"
  | fuel + 1 => do
    if (← peek).isNone then pure []
    else
      let first ← statement fuel
      pure (first :: (← statements fuel))

structure Decoded where
  declarations : List NamedQuantified.NumericDeclaration
  state : State

def decode (input : String) : Except String Decoded := do
  let tokens ← tokenize input
  let (declarations, state) ← statements (tokens.length + 1) {
    tokens, endOffset := input.utf8ByteSize }
  pure { declarations, state }

end Fang.QuantifiedFrontend
