/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Isolated named CNF decoder. Grammar correspondence is a separate obligation. -/
import EqualityNamedSource
import Fang.Input

namespace Fang.EqualityFrontend
open Frontend

def sourceWordChar (character : Char) : Bool :=
  asciiLower character || asciiUpper character || asciiDigit character || character == '_'

def lexAux : Nat → List Char → Nat → Except String (List Token)
  | 0, _, offset => .error s!"resource-exhaustion at byte {offset}: lexer fuel"
  | _ + 1, [], _ => .ok []
  | fuel + 1, character :: rest, offset => do
    if asciiSpace character then lexAux fuel rest (offset + 1)
    else if asciiLower character || asciiUpper character then
      let (tail, following) := rest.span sourceWordChar
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
      let (tail, following) := rest.span sourceWordChar
      if String.ofList (character :: tail) != "$false" then
        .error s!"unsupported at byte {offset}: interpreted symbol"
      else
        let tokens ← lexAux fuel following (offset + tail.length + 1)
        pure ({ text := "$false", offset } :: tokens)
    else if character == '!' && rest.head? == some '=' then
      let tokens ← lexAux fuel rest.tail (offset + 2)
      pure ({ text := "!=", offset } :: tokens)
    else if ['(', ')', ',', '.', '|', '~', '='].contains character then
      let tokens ← lexAux fuel rest (offset + 1)
      pure ({ text := String.singleton character, offset } :: tokens)
    else if ['!', '?', '&', '>', '<', ':', '[', ']', '\'', '"', '%', '/', '_'].contains character || asciiDigit character then
      .error s!"unsupported at byte {offset}: character {character}"
    else .error s!"invalid-syntax at byte {offset}: unexpected character {character}"

def tokenize (input : String) : Except String (List Token) :=
  let characters := input.toList
  match characters.findIdx? (fun character => character.toNat > 127) with
  | some offset => .error s!"invalid-syntax at byte {offset}: ASCII input required"
  | none => lexAux (characters.length + 1) characters 0

mutual
def namedTerm : Nat → Nat → Parser Source.Term
  | 0, _ => fail "resource-exhaustion: named term fuel"
  | fuel + 1, depth => do
    if depth > 64 then fail "resource-exhaustion: source syntax depth"
    let offset ← position
    let name ← consume
    if variableName name then pure (.var name)
    else if lowerName name then
      let arguments ← if (← peek) == some "(" then do
          expect "("
          let arguments ← namedTerms fuel (depth + 1)
          expect ")"
          pure arguments
        else pure []
      pure (.app name arguments)
    else failAt offset "invalid-syntax: expected uninterpreted term or predicate head"

def namedTerms : Nat → Nat → Parser (List Source.Term)
  | 0, _ => fail "resource-exhaustion: named arguments fuel"
  | fuel + 1, depth => do
    let first ← namedTerm fuel depth
    if (← peek) == some "," then
      expect ","
      pure (first :: (← namedTerms fuel depth))
    else pure [first]
end

def literal (fuel : Nat) : Parser EqualitySource.Literal := do
  let negated ← if (← peek) == some "~" then expect "~"; pure true else pure false
  let offset ← position
  let first ← namedTerm fuel 0
  let next ← peek
  if next == some "=" || next == some "!=" then
    if negated then fail "unsupported: use infix != for negative equality"
    let operator ← consume
    let second ← namedTerm fuel 0
    pure ⟨operator == "=", .equal first second⟩
  else match first with
    | .var _ => failAt offset "invalid-syntax: variable cannot be a predicate"
    | .app name arguments => pure ⟨!negated, .predicate name arguments⟩

def literals : Nat → Parser (List EqualitySource.Literal)
  | 0 => fail "resource-exhaustion: source clause fuel"
  | fuel + 1 => do
    let first ← literal fuel
    if (← peek) == some "|" then
      expect "|"
      pure (first :: (← literals fuel))
    else pure [first]

def statement (fuel : Nat) : Parser EqualitySource.Clause := do
  if (← peek) != some "cnf" then fail "unsupported: only cnf declarations"
  expect "cnf"
  expect "("
  let offset ← position
  let name ← consume
  if !lowerName name then failAt offset "invalid-syntax: lower clause name required"
  let state ← get
  if state.clauseNames.contains name then failAt offset "invalid-syntax: duplicate clause name"
  set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
  expect ","
  if (← peek) != some "axiom" then fail "unsupported: only axiom role"
  expect "axiom"
  expect ","
  expect "("
  let body ← if (← peek) == some "$false" then expect "$false"; pure []
    else literals fuel
  expect ")"
  if (← peek) == some "," then fail "unsupported: source annotations"
  expect ")"
  expect "."
  pure ⟨name, body⟩

def statements : Nat → Parser EqualitySource.Problem
  | 0 => fail "resource-exhaustion: source problem fuel"
  | fuel + 1 => do
    if (← peek).isNone then pure []
    else
      let first ← statement fuel
      pure (first :: (← statements fuel))

/-- Named syntax only. Arity tables and numeric encoding are not checked here. -/
def decodeNamed (input : String) : Except String EqualitySource.Problem := do
  let tokens ← tokenize input
  let (problem, state) ← statements (tokens.length + 1) {
    tokens, endOffset := input.utf8ByteSize }
  if !state.tokens.isEmpty then .error "invalid-syntax: trailing tokens"
  else pure problem

end Fang.EqualityFrontend
