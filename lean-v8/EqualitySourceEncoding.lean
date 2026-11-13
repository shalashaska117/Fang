/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent numeric encoding of the parsed named equality problem.
   Ordered first occurrences determine IDs; equality has no predicate ID. -/
import EqualityNamedSource
import Fang.Input

namespace Fang.EqualityFrontend.Encoding
open EqualitySource

def termFunctions : Source.Term → List (String × Nat)
  | .var _ => []
  | .app name arguments => (name, arguments.length) :: arguments.flatMap termFunctions

def termVariables : Source.Term → List String
  | .var name => [name]
  | .app _ arguments => arguments.flatMap termVariables

def atomFunctions : EqualitySource.Atom → List (String × Nat)
  | .predicate _ arguments => arguments.flatMap termFunctions
  | .equal left right => termFunctions left ++ termFunctions right

def atomPredicates : EqualitySource.Atom → List (String × Nat)
  | .predicate name arguments => [(name, arguments.length)]
  | .equal _ _ => []

def atomVariables : EqualitySource.Atom → List String
  | .predicate _ arguments => arguments.flatMap termVariables
  | .equal left right => termVariables left ++ termVariables right

def clauseFunctions (clause : EqualitySource.Clause) : List (String × Nat) :=
  clause.literals.flatMap (fun literal => atomFunctions literal.atom)

def clausePredicates (clause : EqualitySource.Clause) : List (String × Nat) :=
  clause.literals.flatMap (fun literal => atomPredicates literal.atom)

def clauseVariables (clause : EqualitySource.Clause) : List String :=
  (clause.literals.flatMap (fun literal => atomVariables literal.atom)).eraseDups

def firstArity (entries : List (String × Nat)) (name : String) : Option Nat :=
  (entries.find? (fun entry => entry.1 == name)).map Prod.snd

def names (entries : List (String × Nat)) : List String := (entries.map Prod.fst).eraseDups

def namesId (entries : List String) (name : String) : Nat :=
  (Frontend.namedIndex name entries 0).getD 0

def namesValue (entries : List String) (id : Nat) : String := entries[id]?.getD ""

def variables (clause : EqualitySource.Clause) : Source.Variables where
  id := namesId (clauseVariables clause)
  name := namesValue (clauseVariables clause)

def symbols (functions predicates : List (String × Nat)) : Source.Symbols where
  functionId := namesId (names functions)
  functionName := namesValue (names functions)
  predicateId := namesId (names predicates)
  predicateName := namesValue (names predicates)

def signature (functions predicates : List (String × Nat)) : Source.Signature where
  functionArity := firstArity functions
  predicateArity := firstArity predicates

def consistent (entries : List (String × Nat)) : Bool :=
  entries.all (fun entry => firstArity entries entry.1 == some entry.2)

def encodeTerm (symbols : Source.Symbols) (variables : Source.Variables) : Source.Term → Fang.Term
  | .var name => .var (variables.id name)
  | .app name arguments => .app (symbols.functionId name) (arguments.map (encodeTerm symbols variables))

def encodeAtom (symbols : Source.Symbols) (variables : Source.Variables) : EqualitySource.Atom → Equality.Atom
  | .predicate name arguments =>
    .predicate ⟨symbols.predicateId name, arguments.map (encodeTerm symbols variables)⟩
  | .equal left right => .equal (encodeTerm symbols variables left) (encodeTerm symbols variables right)

def encodeLiteral (symbols : Source.Symbols) (variables : Source.Variables) (literal : EqualitySource.Literal) :
    Equality.Literal := ⟨literal.positive, encodeAtom symbols variables literal.atom⟩

def encodeClause (symbols : Source.Symbols) (clause : EqualitySource.Clause) : Equality.Clause :=
  clause.literals.map (encodeLiteral symbols (variables clause))

def symbolTable (entries : List (String × Nat)) : List (String × Nat) :=
  (names entries).map (fun name => (name, (firstArity entries name).getD 0))

structure Encoded where
  functions : List (String × Nat)
  predicates : List (String × Nat)
  clauseNames : List String
  problem : Equality.Problem

def encode (named : EqualitySource.Problem) : Except String Encoded :=
  let functions := named.flatMap clauseFunctions
  let predicates := named.flatMap clausePredicates
  if !(decide (named.map EqualitySource.Clause.name).Nodup) then .error "invalid-syntax: duplicate clause name"
  else if !consistent functions then .error "invalid-syntax: inconsistent function arity"
  else if !consistent predicates then .error "invalid-syntax: inconsistent predicate arity"
  else .ok ⟨symbolTable functions, symbolTable predicates, named.map EqualitySource.Clause.name,
    named.map (encodeClause (symbols functions predicates))⟩

end Fang.EqualityFrontend.Encoding
