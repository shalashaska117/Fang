/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent token productions. Fuel, resource checks and lexical closure
   are not hidden in these relations. The whole-byte boundary adds closure. -/
import ExpandedFofInput

namespace Fang.TptpCandidate.FullFof.Grammar

def Punct (token : Token) (char : Char) : Prop :=
  token.kind = .legacy (.punctuation char)

def NoEquality (tokens : List Token) : Prop :=
  ∀ token rest positive, tokens = token :: rest → token.kind ≠ .legacy (.equality positive)

mutual
inductive TermTokens : List Token → Source.Term → List Token → Prop where
  | variable {token rest name} (kind : token.kind = .legacy (.variable name)) :
      TermTokens (token :: rest) (.var name) rest
  | constant {token rest name} (kind : atomic token.kind = some name)
      (notApplication : isChar '(' rest = false) :
      TermTokens (token :: rest) (.app name []) rest
  | application {token opening input args closing rest name}
      (kind : atomic token.kind = some name) (openParen : Punct opening '(')
      (arguments : ArgumentsTokens input args (closing :: rest)) (closeParen : Punct closing ')') :
      TermTokens (token :: opening :: input) (.app name args) rest

inductive ArgumentsTokens : List Token → List Source.Term → List Token → Prop where
  | one {input value rest} (term : TermTokens input value rest)
      (notComma : isChar ',' rest = false) : ArgumentsTokens input [value] rest
  | more {input value comma middle values rest} (term : TermTokens input value (comma :: middle))
      (separator : Punct comma ',') (tail : ArgumentsTokens middle values rest) :
      ArgumentsTokens input (value :: values) rest
end

inductive AtomTokens : List Token → Formula → List Token → Prop where
  | predicate {input name args rest} (head : TermTokens input (.app name args) rest)
      (noEquality : NoEquality rest) : AtomTokens input (.atom name args) rest
  | equality {input left operator middle right rest positive}
      (head : TermTokens input left (operator :: middle))
      (kind : operator.kind = .legacy (.equality positive))
      (tail : TermTokens middle right rest) :
      AtomTokens input (if positive then .equal left right else .neg (.equal left right)) rest

inductive BindersTokens : List Token → List String → List Token → Prop where
  | one {token name rest} (kind : token.kind = .legacy (.variable name))
      (notComma : isChar ',' rest = false) (notTyped : isChar ':' rest = false) :
      BindersTokens (token :: rest) [name] rest
  | more {token name comma middle names rest} (kind : token.kind = .legacy (.variable name))
      (separator : Punct comma ',') (tail : BindersTokens middle names rest) :
      BindersTokens (token :: comma :: middle) (name :: names) rest

def nextBinary (tokens : List Token) : Option Binary := tokens.head?.bind (binary ∘ Token.kind)

def quantifierKind (universal : Bool) : Kind := .legacy (.punctuation (if universal then '!' else '?'))

mutual
inductive UnitTokens : List Token → Formula → List Token → Prop where
  | truth {token rest} (kind : token.kind = .legacy .truth) : UnitTokens (token :: rest) .truth rest
  | falsity {token rest} (kind : token.kind = .legacy .falsity) : UnitTokens (token :: rest) .falsity rest
  | atom {input body rest} (parsed : AtomTokens input body rest) : UnitTokens input body rest
  | neg {token input body rest} (kind : Punct token '~') (parsed : UnitTokens input body rest) :
      UnitTokens (token :: input) (.neg body) rest
  | group {opening input body closing rest} (openParen : Punct opening '(')
      (parsed : FormulaTokens input body (closing :: rest)) (closeParen : Punct closing ')') :
      UnitTokens (opening :: input) body rest
  | quantified {token opening input names closing colon middle body rest universal}
      (kind : token.kind = quantifierKind universal) (openBracket : Punct opening '[')
      (binders : BindersTokens input names (closing :: colon :: middle))
      (closeBracket : Punct closing ']') (colonKind : Punct colon ':')
      (parsed : UnitTokens middle body rest) :
      UnitTokens (token :: opening :: input) (close universal names body) rest

inductive FormulaTokens : List Token → Formula → List Token → Prop where
  | one {input body rest} (parsed : UnitTokens input body rest)
      (noOperator : nextBinary rest = none) : FormulaTokens input body rest
  | binary {input left middle body rest operator} (first : UnitTokens input left middle)
      (tail : ChainTokens operator left middle body rest) : FormulaTokens input body rest

inductive ChainTokens : Binary → Formula → List Token → Formula → List Token → Prop where
  | one {operator left token middle right rest} (kind : binary token.kind = some operator)
      (parsed : UnitTokens middle right rest)
      (finished : (operator.associative && nextBinary rest == some operator) = false) :
      ChainTokens operator left (token :: middle) (.pair operator left right) rest
  | more {operator left token middle right tail body rest} (kind : binary token.kind = some operator)
      (parsed : UnitTokens middle right tail) (associative : operator.associative = true)
      (following : nextBinary tail = some operator)
      (remaining : ChainTokens operator (.pair operator left right) tail body rest) :
      ChainTokens operator left (token :: middle) body rest
end

end Fang.TptpCandidate.FullFof.Grammar
