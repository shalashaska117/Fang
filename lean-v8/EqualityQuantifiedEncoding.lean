/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent numeric encoding after named parsing. The equality ID follows
   the complete original predicate table and has no source spelling. -/
import EqualityQuantifiedInput
import EqualitySourceEncoding

namespace Fang.QuantifiedEqualityFrontend.Encoding
open NamedQuantifiedEquality
open EqualityFrontend.Encoding (termFunctions termVariables names namesId namesValue
  signature symbols consistent symbolTable encodeTerm)

def atomFunctions : NamedQuantifiedEquality.Atom → List (String × Nat)
  | .predicate _ arguments => arguments.flatMap termFunctions
  | .equal left right => termFunctions left ++ termFunctions right

def atomPredicates : NamedQuantifiedEquality.Atom → List (String × Nat)
  | .predicate name arguments => [(name, arguments.length)]
  | .equal _ _ => []

def atomVariables : NamedQuantifiedEquality.Atom → List String
  | .predicate _ arguments => arguments.flatMap termVariables
  | .equal left right => termVariables left ++ termVariables right

def formulaFunctions : Formula → List (String × Nat)
  | .atom value => atomFunctions value
  | .truth | .falsity => []
  | .neg body | .all _ body | .ex _ body => formulaFunctions body
  | .conj left right | .disj left right | .implies left right =>
      formulaFunctions left ++ formulaFunctions right

def formulaPredicates : Formula → List (String × Nat)
  | .atom value => atomPredicates value
  | .truth | .falsity => []
  | .neg body | .all _ body | .ex _ body => formulaPredicates body
  | .conj left right | .disj left right | .implies left right =>
      formulaPredicates left ++ formulaPredicates right

/-- Source identities are assigned at first occurrence, including unused binders.
    Shadowed spellings share this ID; the rectifier assigns fresh binder IDs. -/
def formulaVariables : Formula → List String
  | .atom value => atomVariables value
  | .truth | .falsity => []
  | .neg body => formulaVariables body
  | .all name body | .ex name body => name :: formulaVariables body
  | .conj left right | .disj left right | .implies left right =>
      formulaVariables left ++ formulaVariables right

def declarationFunctions : Declaration → List (String × Nat)
  | .cnf clause => EqualityFrontend.Encoding.clauseFunctions clause
  | .fof _ body => formulaFunctions body

def declarationPredicates : Declaration → List (String × Nat)
  | .cnf clause => EqualityFrontend.Encoding.clausePredicates clause
  | .fof _ body => formulaPredicates body

def declarationVariables : Declaration → List String
  | .cnf clause => EqualityFrontend.Encoding.clauseVariables clause
  | .fof _ body => (formulaVariables body).eraseDups

def variables (declaration : Declaration) : Source.Variables where
  id := namesId (declarationVariables declaration)
  name := namesValue (declarationVariables declaration)

def encodeAtom (reserved : Nat) (symbols : Source.Symbols) (variables : Source.Variables) :
    NamedQuantifiedEquality.Atom → Fang.Atom
  | .predicate name arguments =>
      ⟨symbols.predicateId name, arguments.map (encodeTerm symbols variables)⟩
  | .equal left right =>
      ⟨reserved, [encodeTerm symbols variables left, encodeTerm symbols variables right]⟩

def encodeFormula (reserved : Nat) (symbols : Source.Symbols) (variables : Source.Variables) :
    Formula → QuantifiedFOF.Formula
  | .atom value => .atom (encodeAtom reserved symbols variables value)
  | .truth => .truth
  | .falsity => .falsity
  | .neg body => .neg (encodeFormula reserved symbols variables body)
  | .conj left right => .conj (encodeFormula reserved symbols variables left) (encodeFormula reserved symbols variables right)
  | .disj left right => .disj (encodeFormula reserved symbols variables left) (encodeFormula reserved symbols variables right)
  | .implies left right => .implies (encodeFormula reserved symbols variables left) (encodeFormula reserved symbols variables right)
  | .all name body => .all (variables.id name) (encodeFormula reserved symbols variables body)
  | .ex name body => .ex (variables.id name) (encodeFormula reserved symbols variables body)

def sourceAtom : EqualitySource.Atom → NamedQuantifiedEquality.Atom
  | .predicate name arguments => .predicate name arguments
  | .equal left right => .equal left right

def encodeLiteral (reserved : Nat) (symbols : Source.Symbols) (variables : Source.Variables)
    (literal : EqualitySource.Literal) : Fang.Literal :=
  ⟨literal.positive, encodeAtom reserved symbols variables (sourceAtom literal.atom)⟩

inductive EncodedDeclaration where
  | cnf : String → Fang.Clause → EncodedDeclaration
  | fof : String → QuantifiedFOF.Formula → EncodedDeclaration

def encodeDeclaration (reserved : Nat) (symbols : Source.Symbols) (declaration : Declaration) :
    EncodedDeclaration :=
  match declaration with
  | .cnf clause => .cnf clause.name (clause.literals.map (encodeLiteral reserved symbols (variables declaration)))
  | .fof name body => .fof name (encodeFormula reserved symbols (variables declaration) body)

structure Encoded where
  functions : List (String × Nat)
  originalPredicates : List (String × Nat)
  equalityId : Nat
  predicateArities : List Nat
  declarations : List EncodedDeclaration

/-- Every original declaration contributes before the equality slot is reserved.
    No user name can allocate or alias that extra slot. -/
def encode (named : List Declaration) : Except String Encoded :=
  let functions := named.flatMap declarationFunctions
  let predicates := named.flatMap declarationPredicates
  let table := symbolTable predicates
  let reserved := (names predicates).length
  if !(decide (named.map Declaration.name).Nodup) then .error "invalid-syntax: duplicate declaration name"
  else if !consistent functions then .error "invalid-syntax: inconsistent function arity"
  else if !consistent predicates then .error "invalid-syntax: inconsistent predicate arity"
  else .ok ⟨symbolTable functions, table, reserved, table.map Prod.snd ++ [2],
    named.map (encodeDeclaration reserved (symbols functions predicates))⟩

end Fang.QuantifiedEqualityFrontend.Encoding
