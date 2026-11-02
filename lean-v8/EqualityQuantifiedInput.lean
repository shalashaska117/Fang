/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent named decoder. Numeric encoding and byte correspondence are separate. -/
import EqualityQuantifiedNamed
import EqualitySourceInput

namespace Fang.NamedQuantifiedEquality

inductive Declaration where
  | cnf : EqualitySource.Clause → Declaration
  | fof : String → Formula → Declaration

def Declaration.name : Declaration → String
  | .cnf clause => clause.name
  | .fof name _ => name

def Formula.bind (universal : Bool) (names : List String) (body : Formula) : Formula :=
  names.foldr (fun name tail => if universal then .all name tail else .ex name tail) body

end Fang.NamedQuantifiedEquality

namespace Fang.QuantifiedEqualityFrontend
open Frontend NamedQuantifiedEquality

def lexAux : Nat → List Char → Nat → Except String (List Token)
  | 0, _, offset => .error s!"resource-exhaustion at byte {offset}: lexer fuel"
  | _ + 1, [], _ => .ok []
  | fuel + 1, character :: rest, offset => do
    if asciiSpace character then lexAux fuel rest (offset + 1)
    else if asciiLower character || asciiUpper character then
      let (tail, following) := rest.span EqualityFrontend.sourceWordChar
      if asciiLower character then
        if let some index := tail.findIdx? asciiUpper then
          .error s!"invalid-syntax at byte {offset + 1 + index}: uppercase in lower identifier"
        else
          let tokens ← lexAux fuel following (offset + tail.length + 1)
          pure ({ text := String.ofList (character :: tail), offset } :: tokens)
      else
        let tokens ← lexAux fuel following (offset + tail.length + 1)
        pure ({ text := String.ofList (character :: tail), offset } :: tokens)
    else if character == '$' then
      let (tail, following) := rest.span EqualityFrontend.sourceWordChar
      let text := String.ofList (character :: tail)
      if text != "$false" && text != "$true" then
        .error s!"unsupported at byte {offset}: interpreted symbol"
      else
        let tokens ← lexAux fuel following (offset + tail.length + 1)
        pure ({ text, offset } :: tokens)
    else if character == '=' && rest.head? == some '>' then
      let tokens ← lexAux fuel rest.tail (offset + 2)
      pure ({ text := "=>", offset } :: tokens)
    else if character == '!' && rest.head? == some '=' then
      let tokens ← lexAux fuel rest.tail (offset + 2)
      pure ({ text := "!=", offset } :: tokens)
    else if character == '~' && (rest.head? == some '&' || rest.head? == some '|') then
      .error s!"unsupported at byte {offset}: NAND/NOR"
    else if ['(', ')', ',', '.', '|', '~', '=', '&', '!', '?', '[', ']', ':'].contains character then
      let tokens ← lexAux fuel rest (offset + 1)
      pure ({ text := String.singleton character, offset } :: tokens)
    else if ['>', '<', '\'', '"', '%', '/', '_'].contains character || asciiDigit character then
      .error s!"unsupported at byte {offset}: character {character}"
    else .error s!"invalid-syntax at byte {offset}: unexpected character {character}"

def tokenize (input : String) : Except String (List Token) :=
  let characters := input.toList
  match characters.findIdx? (fun character => character.toNat > 127) with
  | some offset => .error s!"invalid-syntax at byte {offset}: ASCII input required"
  | none => lexAux (characters.length + 1) characters 0

mutual
def termWithin (bound : List String) : Source.Term → Bool
  | .var name => bound.contains name
  | .app _ arguments => termsWithin bound arguments
def termsWithin (bound : List String) : List Source.Term → Bool
  | [] => true
  | term :: rest => termWithin bound term && termsWithin bound rest
end

def atomWithin (bound : List String) : NamedQuantifiedEquality.Atom → Bool
  | .predicate _ arguments => termsWithin bound arguments
  | .equal left right => termWithin bound left && termWithin bound right

def formulaWithin (bound : List String) : Formula → Bool
  | .atom value => atomWithin bound value
  | .truth | .falsity => true
  | .neg body => formulaWithin bound body
  | .conj left right | .disj left right | .implies left right =>
      formulaWithin bound left && formulaWithin bound right
  | .all name body | .ex name body => formulaWithin (name :: bound) body

/-- Neutral named terms avoid assigning a predicate ID to an equality operand. -/
def atom (fuel : Nat) : Parser Formula := do
  let offset ← position
  let first ← EqualityFrontend.namedTerm fuel 0
  let next ← peek
  if next == some "=" || next == some "!=" then
    let operator ← consume
    let second ← EqualityFrontend.namedTerm fuel 0
    let value := Formula.atom (.equal first second)
    pure (if operator == "=" then value else .neg value)
  else match first with
    | .var _ => failAt offset "invalid-syntax: variable cannot be a predicate"
    | .app name arguments => pure (.atom (.predicate name arguments))

def binders : Nat → Parser (List String)
  | 0 => fail "resource-exhaustion: binder decoder fuel"
  | fuel + 1 => do
    let offset ← position
    let name ← consume
    if !variableName name then failAt offset "invalid-syntax: expected a variable binder"
    let delimiter ← peek
    if delimiter == some "]" then expect "]"; pure [name]
    else if delimiter == some "," then expect ","; pure (name :: (← binders fuel))
    else if delimiter == some ":" then fail "unsupported: typed binders"
    else fail "invalid-syntax: expected comma or closing bracket"

def formula : Nat → Nat → Parser Formula
  | 0, _ => fail "resource-exhaustion: formula decoder fuel"
  | fuel + 1, depth => do
    if depth > 64 then fail "resource-exhaustion: formula syntax depth"
    let next ← peek
    if next == some "$true" then expect "$true"; pure .truth
    else if next == some "$false" then expect "$false"; pure .falsity
    else if next == some "~" then expect "~"; pure (.neg (← formula fuel (depth + 1)))
    else if next == some "!" || next == some "?" then
      discard consume
      expect "["
      let names ← binders fuel
      expect ":"
      pure ((← formula fuel (depth + 1)).bind (next == some "!") names)
    else if next == some "(" then
      expect "("
      let left ← formula fuel (depth + 1)
      let operator ← peek
      if operator == some "&" || operator == some "|" || operator == some "=>" then
        discard consume
        let right ← formula fuel (depth + 1)
        expect ")"
        if operator == some "&" then pure (.conj left right)
        else if operator == some "|" then pure (.disj left right)
        else pure (.implies left right)
      else expect ")"; pure left
    else atom fuel

def statement (fuel : Nat) : Parser Declaration := do
  if (← peek) == some "cnf" then pure (.cnf (← EqualityFrontend.statement fuel))
  else if (← peek) == some "fof" then
    expect "fof"
    expect "("
    let offset ← position
    let name ← consume
    if !lowerName name then failAt offset "invalid-syntax: lower statement name required"
    let state ← get
    if state.clauseNames.contains name then failAt offset "invalid-syntax: duplicate statement name"
    set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
    expect ","
    if (← peek) != some "axiom" then fail "unsupported: only axiom role"
    expect "axiom"
    expect ","
    let body ← formula fuel 0
    if !formulaWithin [] body then fail "invalid-syntax: free FOF variable"
    if (← peek) == some "," then fail "unsupported: source annotations"
    expect ")"
    expect "."
    pure (.fof name body)
  else
    let kind ← peek
    fail (if ["include", "tff", "thf", "tcf"].any (fun name => kind == some name)
      then "unsupported: only CNF and FOF declarations"
      else "invalid-syntax: expected CNF or FOF declaration")

def statements : Nat → Parser (List Declaration)
  | 0 => fail "resource-exhaustion: declaration decoder fuel"
  | fuel + 1 => do
    if (← peek).isNone then pure []
    else pure ((← statement fuel) :: (← statements fuel))

/-- Named syntax and lexical closure only; no arity table or numeric encoding. -/
def decodeNamed (input : String) : Except String (List Declaration) := do
  let tokens ← tokenize input
  let (declarations, state) ← statements (tokens.length + 1) {
    tokens, endOffset := input.utf8ByteSize }
  if !state.tokens.isEmpty then .error "invalid-syntax: trailing tokens"
  else pure declarations

end Fang.QuantifiedEqualityFrontend
