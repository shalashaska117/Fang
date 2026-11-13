/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent unit/list/pair parser. Resource policy is explicit below; this
   file does not claim exact Rust counters or reverse grammar acceptance. -/
import FofLexer
import FofEncoding

namespace Fang.TptpCandidate.FullFof

def offset (endOffset : Nat) (tokens : List Token) : Nat :=
  (tokens.head?.map Token.start).getD endOffset

def failure {α : Type} (kind : ErrorKind) (endOffset : Nat) (tokens : List Token) : Except Error α :=
  .error ⟨kind, offset endOffset tokens⟩

def isChar (char : Char) (tokens : List Token) : Bool :=
  tokens.head?.map Token.kind == some (.legacy (.punctuation char))

def expect (char : Char) (endOffset : Nat) (tokens : List Token) : Except Error (Token × List Token) :=
  match tokens with
  | token :: rest =>
    if token.kind = .legacy (.punctuation char) then .ok (token, rest)
    else failure .invalid endOffset tokens
  | [] => failure .invalid endOffset tokens

def atomic : Kind → Option String
  | .legacy (.lower name) | .legacy (.quoted name) => some name
  | _ => none

def binary : Kind → Option Binary
  | .legacy (.punctuation '&') => some .conj
  | .legacy (.punctuation '|') => some .disj
  | .legacy .implies => some .implies
  | .reverse => some .reverse
  | .iff => some .iff
  | .xor => some .xor
  | .nand => some .nand
  | .nor => some .nor
  | _ => none

def Binary.extra : Binary → Nat
  | .nand | .nor | .iff => 2
  | .xor => 3
  | _ => 1

def Binary.associative : Binary → Bool
  | .conj | .disj => true
  | _ => false

mutual
def term : Nat → Nat → Option (List String) → Nat → List Token →
    Except Error (Source.Term × List Token)
  | 0, _, _, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, scope, endOffset, tokens => do
    if depth > 64 then failure .resource endOffset tokens
    let token :: rest := tokens | failure .invalid endOffset tokens
    match token.kind with
    | .legacy (.variable name) =>
      if let some bound := scope then
        if !bound.contains name then failure .invalid endOffset tokens
      pure (.var name, rest)
    | .legacy (.integer _) => failure .unsupported endOffset tokens
    | kind =>
      let some name := atomic kind | failure .invalid endOffset tokens
      if isChar '(' rest then
        let (args, tail) ← arguments fuel (depth + 1) scope endOffset rest.tail
        let (_, final) ← expect ')' endOffset tail
        pure (.app name args, final)
      else pure (.app name [], rest)

def arguments : Nat → Nat → Option (List String) → Nat → List Token →
    Except Error (List Source.Term × List Token)
  | 0, _, _, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, scope, endOffset, tokens => do
    let (first, rest) ← term fuel depth scope endOffset tokens
    if isChar ',' rest then
      let (tail, final) ← arguments fuel depth scope endOffset rest.tail
      pure (first :: tail, final)
    else pure ([first], rest)
end

/-- The neutral head is classified after the equality lookahead. Only its
    arguments become function occurrences when it is a predicate. -/
def atom (fuel : Nat) (scope : Option (List String)) (endOffset : Nat) (tokens : List Token) :
    Except Error (Formula × List Token) := do
  let (head, rest) ← term fuel 0 scope endOffset tokens
  match rest with
  | token :: afterOperator =>
    if let .legacy (.equality positive) := token.kind then
      let (right, final) ← term fuel 0 scope endOffset afterOperator
      let equality := Formula.equal head right
      pure (if positive then equality else .neg equality, final)
    else
      match head with
      | .var _ => failure .invalid endOffset tokens
      | .app name args => pure (.atom name args, rest)
  | [] =>
    match head with
    | .var _ => failure .invalid endOffset tokens
    | .app name args => pure (.atom name args, rest)

def binders : Nat → Nat → List Token → Except Error (List String × List Token)
  | 0, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, endOffset, tokens => do
    let token :: rest := tokens | failure .invalid endOffset tokens
    let .legacy (.variable name) := token.kind | failure .invalid endOffset tokens
    if isChar ':' rest then failure .unsupported endOffset rest
    if isChar ',' rest then
      let (tail, final) ← binders fuel endOffset rest.tail
      pure (name :: tail, final)
    else pure ([name], rest)

def close (universal : Bool) (names : List String) (body : Formula) : Formula :=
  names.foldr (fun name rest => if universal then .all name rest else .ex name rest) body

def Formula.height : Formula → Nat
  | .atom _ _ | .equal _ _ | .truth | .falsity => 1
  | .neg body | .all _ body | .ex _ body => body.height + 1
  | .pair operator left right => max left.height right.height + operator.extra

def checked (depth endOffset : Nat) (original : List Token) (body : Formula) (rest : List Token) :
    Except Error (Formula × List Token) :=
  if depth + body.height - 1 > 64 then failure .resource endOffset original
  else .ok (body, rest)

mutual
def unit : Nat → Nat → List String → Nat → List Token → Except Error (Formula × List Token)
  | 0, _, _, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, tokens => do
    if depth > 64 then failure .resource endOffset tokens
    let token :: rest := tokens | failure .invalid endOffset tokens
    match token.kind with
    | .legacy .truth => pure (.truth, rest)
    | .legacy .falsity => pure (.falsity, rest)
    | .legacy (.punctuation '~') =>
      let (body, final) ← unit fuel (depth + 1) bound endOffset rest
      checked depth endOffset tokens (.neg body) final
    | .legacy (.punctuation '(') =>
      let (body, tail) ← formula fuel (depth + 1) bound endOffset rest
      let (_, final) ← expect ')' endOffset tail
      pure (body, final)
    | .legacy (.punctuation '!') | .legacy (.punctuation '?') =>
      let (_, tail) ← expect '[' endOffset rest
      let (names, tail) ← binders (tokens.length + 1) endOffset tail
      if names.length + depth > 64 then failure .resource endOffset tokens
      let (_, tail) ← expect ']' endOffset tail
      let (_, tail) ← expect ':' endOffset tail
      let (body, final) ← unit fuel (depth + names.length) (names ++ bound) endOffset tail
      checked depth endOffset tokens (close (token.kind == .legacy (.punctuation '!')) names body) final
    | .legacy (.integer _) => failure .unsupported endOffset tokens
    | _ =>
      let (body, rest) ← atom (2 * tokens.length + 1) (some bound) endOffset tokens
      checked depth endOffset tokens body rest

def formula : Nat → Nat → List String → Nat → List Token → Except Error (Formula × List Token)
  | 0, _, _, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, tokens => do
    let (left, rest) ← unit fuel depth bound endOffset tokens
    match rest with
    | [] => pure (left, rest)
    | next :: _ =>
      match binary next.kind with
      | none => pure (left, rest)
      | some operator => chain fuel depth bound endOffset operator left rest

def chain : Nat → Nat → List String → Nat → Binary → Formula → List Token →
    Except Error (Formula × List Token)
  | 0, _, _, endOffset, _, _, tokens => failure .resource endOffset tokens
  | fuel + 1, depth, bound, endOffset, operator, left, tokens => do
    let next :: rest := tokens | failure .invalid endOffset tokens
    if binary next.kind != some operator then failure .internal endOffset tokens
    let (right, tail) ← unit fuel (depth + operator.extra) bound endOffset rest
    let body := Formula.pair operator left right
    let (_, _) ← checked depth endOffset tokens body tail
    if operator.associative && tail.head?.bind (binary ∘ Token.kind) == some operator then
      chain fuel depth bound endOffset operator body tail
    else pure (body, tail)
end

def cnfLiteral (endOffset : Nat) (tokens : List Token) : Except Error (Formula × List Token) := do
  let negative := isChar '~' tokens
  let body := if negative then tokens.tail else tokens
  if isChar '!' body || isChar '?' body then failure .unsupported endOffset body
  let (value, rest) ← atom (2 * body.length + 1) none endOffset body
  if negative then
    match value with
    | .atom _ _ => pure (.neg value, rest)
    | _ => failure .unsupported endOffset rest
  else pure (value, rest)

def cnfLiterals : Nat → Nat → List Token → Except Error (List Formula × List Token)
  | 0, endOffset, tokens => failure .resource endOffset tokens
  | fuel + 1, endOffset, tokens => do
    let (first, rest) ← cnfLiteral endOffset tokens
    if isChar '|' rest then
      let (tail, final) ← cnfLiterals fuel endOffset rest.tail
      pure (first :: tail, final)
    else if rest.head?.map Token.kind == some (.legacy .implies) || isChar '&' rest then
      failure .unsupported endOffset rest
    else pure ([first], rest)

inductive Body where
  | cnf : List Formula → Body
  | fof : Formula → Body
  deriving Repr

def Body.formula : Body → Formula
  | .cnf literals => literals.foldr (Formula.pair .disj) .falsity
  | .fof value => value

structure Declaration where
  name : Name
  body : Body
  start : Nat
  stop : Nat
  bodyStart : Nat
  bodyStop : Nat
  deriving Repr

def declaration (seen : List Name) (endOffset : Nat) (tokens : List Token) :
    Except Error (Declaration × List Token) := do
  let keyword :: rest := tokens | failure .invalid endOffset tokens
  let isCnf ← match keyword.kind with
    | .legacy (.lower "cnf") => pure true
    | .legacy (.lower "fof") => pure false
    | .legacy (.lower "include") | .legacy (.lower "tff") | .legacy (.lower "thf") |
        .legacy (.lower "tcf") => failure .unsupported endOffset tokens
    | _ => failure .invalid endOffset tokens
  let (_, rest) ← expect '(' endOffset rest
  let nameToken :: rest := rest | failure .invalid endOffset rest
  let .legacy nameKind := nameToken.kind | failure .invalid endOffset (nameToken :: rest)
  let some name := nameKind.name | failure .invalid endOffset (nameToken :: rest)
  if seen.contains name then failure .invalid endOffset (nameToken :: rest)
  let (_, rest) ← expect ',' endOffset rest
  let role :: rest := rest | failure .invalid endOffset rest
  match role.kind with
  | .legacy (.lower "axiom") => pure ()
  | .legacy (.lower _) => failure .unsupported endOffset (role :: rest)
  | _ => failure .invalid endOffset (role :: rest)
  let (_, originalBody) ← expect ',' endOffset rest
  let (body, rest) ← if isCnf then do
      let (_, rest) ← expect '(' endOffset originalBody
      let (literals, rest) ← match rest with
        | token :: tail => match token.kind with
          | .legacy .falsity => pure ([], tail)
          | .legacy .truth => failure .unsupported endOffset rest
          | _ => cnfLiterals (rest.length + 1) endOffset rest
        | [] => failure .invalid endOffset rest
      let (_, rest) ← expect ')' endOffset rest
      pure (Body.cnf literals, rest)
    else do
      let (body, rest) ← formula (3 * originalBody.length + 1) 1 [] endOffset originalBody
      pure (Body.fof body, rest)
  let bodyStop := ((originalBody.take (originalBody.length - rest.length)).getLast?.map Token.stop).getD endOffset
  if isChar ',' rest then failure .unsupported endOffset rest
  let (_, rest) ← expect ')' endOffset rest
  let (dot, rest) ← expect '.' endOffset rest
  pure (⟨name, body, keyword.start, dot.stop, offset endOffset originalBody, bodyStop⟩, rest)

def declarations : Nat → List Name → Nat → List Token → Except Error (List Declaration)
  | 0, _, endOffset, tokens => failure .resource endOffset tokens
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, tokens@(_ :: _) => do
    if seen.length ≥ 1000 then failure .resource endOffset tokens
    let (first, rest) ← declaration seen endOffset tokens
    let tail ← declarations fuel (first.name :: seen) endOffset rest
    pure (first :: tail)

def source (declarations : List Declaration) : List Formula :=
  declarations.map (Body.formula ∘ Declaration.body)

def decodeBytes (input : List UInt8) (maximumBytes : Nat := 1048576) : Except Error (List Declaration) := do
  let tokens ← tokenizeBytes input maximumBytes
  declarations (tokens.length + 1) [] input.length tokens

def decode (input : String) : Except Error (List Declaration) :=
  decodeBytes input.toUTF8.data.toList

theorem encoded_satisfiable_iff (declarations : List Declaration) :
    Satisfiable (source declarations) ↔ EncodedSatisfiable (source declarations) :=
  satisfiable_iff (source declarations)

end Fang.TptpCandidate.FullFof
