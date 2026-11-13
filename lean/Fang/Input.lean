import Fang.Logic

/-
Copyright (c) 2026 Pietro Pellegrino. Released under the BSD 3-Clause license.

Independent decoder for the documented ASCII CNF subset.
This total program has not yet been proved equivalent to a declarative grammar.
-/

namespace Fang
namespace Frontend

structure Token where
  text : String
  offset : Nat
  deriving Repr, BEq

structure Symbol where
  name : String
  arity : Option Nat
  deriving Repr

structure State where
  tokens : List Token
  endOffset : Nat
  functions : List Symbol := []
  predicates : List Symbol := []
  variables : List String := []
  clauseNames : List String := []

abbrev Parser := StateT State (Except String)

def asciiLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def asciiUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def asciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def asciiSpace (c : Char) : Bool := c == ' ' || (9 ≤ c.toNat && c.toNat ≤ 13)
def wordChar (c : Char) : Bool :=
  asciiLower c || asciiUpper c || asciiDigit c || c == '_' || c == '$' || c == '-'

def lowerName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => asciiLower c && cs.all (fun x => asciiLower x || asciiDigit x || x == '_')

def variableName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => asciiUpper c &&
      cs.all (fun x => asciiLower x || asciiUpper x || asciiDigit x || x == '_')

def lexAux : Nat → List Char → Nat → Except String (List Token)
  | 0, _, offset => .error s!"resource-exhaustion at byte {offset}: lexer fuel"
  | _ + 1, [], _ => .ok []
  | fuel + 1, c :: cs, offset => do
    if asciiSpace c then
      lexAux fuel cs (offset + 1)
    else if wordChar c then
      let (tail, rest) := cs.span wordChar
      let chars := c :: tail
      let remaining ← lexAux fuel rest (offset + chars.length)
      pure ({ text := String.ofList chars, offset } :: remaining)
    else if ['(', ')', ',', '.', '|', '~'].contains c then
      let remaining ← lexAux fuel cs (offset + 1)
      pure ({ text := String.singleton c, offset } :: remaining)
    else if ['=', '!', '?', ':', '[', ']', '\'', '"', '%', '/'].contains c then
      .error s!"unsupported at byte {offset}: character {c}"
    else
      .error s!"invalid-syntax at byte {offset}: unexpected character {c}"

def tokenize (input : String) : Except String (List Token) :=
  let chars := input.toList
  match chars.findIdx? (fun c => c.toNat > 127) with
  | some offset => .error s!"unsupported at byte {offset}: input must contain ASCII bytes only (no BOM)"
  | none => lexAux (chars.length + 1) chars 0

def position : Parser Nat := do
  let state ← get
  pure (match state.tokens with
    | [] => state.endOffset
    | token :: _ => token.offset)

def failAt (offset : Nat) (reason : String) : Parser α :=
  throw s!"{reason} at byte {offset}"

def fail (reason : String) : Parser α := do
  failAt (← position) reason

def peek : Parser (Option String) := do
  pure ((← get).tokens.head?.map Token.text)

def consume : Parser String := do
  let state ← get
  match state.tokens with
  | [] => fail "invalid-syntax: unexpected EOF"
  | token :: rest =>
    set { state with tokens := rest }
    pure token.text

def expect (wanted : String) : Parser Unit := do
  let next ← peek
  if next != some wanted then fail s!"invalid-syntax: expected '{wanted}'"
  else discard consume

def natural : Parser Nat := do
  let next ← peek
  match next with
  | some text =>
    if text.isEmpty || !text.toList.all asciiDigit then
      fail "invalid-syntax: expected a natural number"
    else
      match text.toNat? with
      | some value => discard consume; pure value
      | none => fail "invalid-syntax: invalid natural number"
  | none => fail "invalid-syntax: expected a natural number"

def namedIndex (name : String) : List String → Nat → Option Nat
  | [], _ => none
  | candidate :: rest, index =>
    if name == candidate then some index else namedIndex name rest (index + 1)

def symbolIndex (name : String) : List Symbol → Nat → Option Nat
  | [], _ => none
  | candidate :: rest, index =>
    if name == candidate.name then some index else symbolIndex name rest (index + 1)

def reserveSymbol (predicate : Bool) (name : String) : Parser Nat := do
  let state ← get
  let symbols := if predicate then state.predicates else state.functions
  match symbolIndex name symbols 0 with
  | some id => pure id
  | none =>
    let updated := symbols ++ [{ name, arity := none }]
    if predicate then set { state with predicates := updated }
    else set { state with functions := updated }
    pure symbols.length

def checkArity (predicate : Bool) (id arity offset : Nat) : Parser Unit := do
  let state ← get
  let symbols := if predicate then state.predicates else state.functions
  match symbols[id]? with
  | none => fail "invalid-syntax: missing symbol"
  | some symbol =>
    match symbol.arity with
    | some previous =>
      if previous != arity then failAt offset s!"invalid-syntax: inconsistent arity for '{symbol.name}'"
    | none =>
      let updated := symbols.set id { symbol with arity := some arity }
      if predicate then set { state with predicates := updated }
      else set { state with functions := updated }

def variableId (name : String) : Parser Nat := do
  let state ← get
  match namedIndex name state.variables 0 with
  | some id => pure id
  | none =>
    set { state with variables := state.variables ++ [name] }
    pure state.variables.length

mutual
  def term : Nat → Parser Term
    | 0 => fail "resource-exhaustion: term decoder fuel"
    | fuel + 1 => do
      let offset ← position
      let name ← consume
      if variableName name then
        pure (.var (← variableId name))
      else if lowerName name then
        let id ← reserveSymbol false name
        let args ← if (← peek) == some "(" then do
            expect "("
            let args ← terms fuel
            expect ")"
            pure args
          else pure []
        checkArity false id args.length offset
        pure (.app id args)
      else failAt offset s!"unsupported: expected an uninterpreted term, found '{name}'"

  def terms : Nat → Parser (List Term)
    | 0 => fail "resource-exhaustion: argument decoder fuel"
    | fuel + 1 => do
      let first ← term fuel
      if (← peek) == some "," then
        expect ","
        pure (first :: (← terms fuel))
      else pure [first]
end

def literal (fuel : Nat) : Parser Literal := do
  let positive ← if (← peek) == some "~" then expect "~"; pure false else pure true
  let offset ← position
  let name ← consume
  if !lowerName name then failAt offset s!"unsupported: expected a predicate, found '{name}'"
  let pred ← reserveSymbol true name
  let args ← if (← peek) == some "(" then do
      expect "("
      let args ← terms fuel
      expect ")"
      pure args
    else pure []
  checkArity true pred args.length offset
  pure { positive, atom := { pred, args } }

def literals : Nat → Parser Clause
  | 0 => fail "resource-exhaustion: clause decoder fuel"
  | fuel + 1 => do
    let first ← literal fuel
    if (← peek) == some "|" then
      expect "|"
      pure (first :: (← literals fuel))
    else pure [first]

def statement (fuel : Nat) : Parser Clause := do
  if (← peek) != some "cnf" then fail "unsupported: only cnf declarations are supported"
  expect "cnf"
  expect "("
  let offset ← position
  let name ← consume
  if !lowerName name then failAt offset "invalid-syntax: clause name must be a lower-case identifier"
  let state ← get
  if state.clauseNames.contains name then failAt offset s!"invalid-syntax: duplicate clause name '{name}'"
  set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
  expect ","
  if (← peek) != some "axiom" then fail "unsupported: only the axiom role is supported"
  expect "axiom"
  expect ","
  expect "("
  let body ← if (← peek) == some "$false" then expect "$false"; pure []
    else literals fuel
  expect ")"
  expect ")"
  expect "."
  pure body

def statements : Nat → Parser Problem
  | 0 => fail "resource-exhaustion: problem decoder fuel"
  | fuel + 1 => do
    if (← peek).isNone then pure []
    else
      let first ← statement fuel
      pure (first :: (← statements fuel))

end Frontend

structure DecodedProblem where
  problem : Problem
  functionArities : List Nat
  predicateArities : List Nat
  deriving Repr

def decodeProblemWithSignature (input : String) : Except String DecodedProblem := do
  let tokens ← Frontend.tokenize input
  let (problem, state) ← Frontend.statements (tokens.length + 1) {
    tokens, endOffset := input.utf8ByteSize
  }
  pure {
    problem
    functionArities := state.functions.map (fun symbol => symbol.arity.getD 0)
    predicateArities := state.predicates.map (fun symbol => symbol.arity.getD 0)
  }

def decodeProblem (input : String) : Except String Problem := do
  pure (← decodeProblemWithSignature input).problem

end Fang
