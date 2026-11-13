/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Role metadata wraps the accepted body parser; original tokens remain explicit. -/
import CnfBooleanByteSemantics
import RoleSemantics

namespace Fang.TptpCandidate.Roles.Bytes
open FullFof

def roleName : Role → String
  | .axiomRole => "axiom"
  | .hypothesis => "hypothesis"
  | .definition => "definition"
  | .assumption => "assumption"
  | .lemma => "lemma"
  | .theoremRole => "theorem"
  | .corollary => "corollary"
  | .conjecture => "conjecture"
  | .negatedConjecture => "negated_conjecture"
  | .plain => "plain"
  | .typeRole => "type"
  | .interpretation => "interpretation"
  | .logic => "logic"
  | .unknown => "unknown"

def roleOfName : String → Option Role
  | "axiom" => some .axiomRole
  | "hypothesis" => some .hypothesis
  | "definition" => some .definition
  | "assumption" => some .assumption
  | "lemma" => some .lemma
  | "theorem" => some .theoremRole
  | "corollary" => some .corollary
  | "conjecture" => some .conjecture
  | "negated_conjecture" => some .negatedConjecture
  | "plain" => some .plain
  | "type" => some .typeRole
  | "interpretation" => some .interpretation
  | "logic" => some .logic
  | "unknown" => some .unknown
  | _ => none

def readRole (endOffset : Nat) (token : FullFof.Token) : Except Error Role := do
  let .legacy (.lower word) := token.kind | FullFof.failure .invalid endOffset [token]
  let some role := roleOfName word | FullFof.failure .invalid endOffset [token]
  match classify role with
  | .ok _ => pure role
  | .error .unknownRole => FullFof.failure .invalid endOffset [token]
  | .error _ => FullFof.failure .unsupported endOffset [token]

structure Header where
  keyword : FullFof.Token
  opening : FullFof.Token
  name : FullFof.Token
  comma : FullFof.Token
  role : FullFof.Token
  rest : List FullFof.Token

def Header.tokens (header : Header) : List FullFof.Token :=
  header.keyword :: header.opening :: header.name :: header.comma :: header.role :: header.rest

/-- Only the role kind changes for the reused axiom-role reader. The original
    role and every token span remain in Header and the returned Entry. -/
def Header.patched (header : Header) : List FullFof.Token :=
  header.keyword :: header.opening :: header.name :: header.comma ::
    { header.role with kind := .legacy (.lower "axiom") } :: header.rest

def header? : List FullFof.Token → Option Header
  | keyword :: opening :: name :: comma :: role :: rest =>
      some ⟨keyword, opening, name, comma, role, rest⟩
  | _ => none

structure Entry where
  original : FullFof.Declaration
  role : Role
  roleStart : Nat
  roleStop : Nat

def invalidGoal (header : Header) (role : Role) : Bool :=
  decide (role = .conjecture) && (header.keyword.kind == .legacy (.lower "cnf"))

def declaration (seen : List Name) (endOffset : Nat) (tokens : List FullFof.Token) :
    Except Error (Entry × List FullFof.Token) := do
  let some header := header? tokens | FullFof.failure .invalid endOffset tokens
  let role ← readRole endOffset header.role
  if invalidGoal header role then FullFof.failure .invalid endOffset tokens
  let (original, rest) ← CnfBoolean.declaration seen endOffset header.patched
  pure (⟨original, role, header.role.start, header.role.stop⟩, rest)

def declarations : Nat → List Name → Nat → List FullFof.Token → Except Error (List Entry)
  | 0, _, endOffset, tokens => FullFof.failure .resource endOffset tokens
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, tokens@(_ :: _) => do
    if seen.length ≥ 1000 then FullFof.failure .resource endOffset tokens
    let (first, rest) ← declaration seen endOffset tokens
    let tail ← declarations fuel (first.original.name :: seen) endOffset rest
    pure (first :: tail)

def modesValid (values : List Entry) : Bool :=
  !(values.any (fun value => decide (value.role = .conjecture)) &&
    values.any (fun value => decide (value.role = .negatedConjecture)))

def decodeBytes (input : List UInt8) (maximumBytes : Nat := 1048576) : Except Error (List Entry) := do
  let tokens ← FullFof.tokenizeBytes input maximumBytes
  let values ← declarations (tokens.length + 1) [] input.length tokens
  if modesValid values then pure values else FullFof.failure .unsupported input.length []

def decode (input : String) : Except Error (List Entry) := decodeBytes input.toUTF8.data.toList

end Fang.TptpCandidate.Roles.Bytes
