/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import FofFormulaSound

namespace Fang.TptpCandidate.FullFof.Grammar

inductive CnfLiteralTokens : List Token → Formula → List Token → Prop where
  | positive {input body rest} (atom : AtomTokens input body rest) : CnfLiteralTokens input body rest
  | negative {token input name args rest} (negative : Punct token '~')
      (atom : AtomTokens input (.atom name args) rest) :
      CnfLiteralTokens (token :: input) (.neg (.atom name args)) rest

inductive CnfLiteralsTokens : List Token → List Formula → List Token → Prop where
  | one {input value rest} (first : CnfLiteralTokens input value rest)
      (notBar : isChar '|' rest = false) : CnfLiteralsTokens input [value] rest
  | more {input value separator middle values rest}
      (first : CnfLiteralTokens input value (separator :: middle)) (bar : Punct separator '|')
      (tail : CnfLiteralsTokens middle values rest) : CnfLiteralsTokens input (value :: values) rest

inductive BodyTokens : List Token → Body → List Token → Prop where
  | fof {input value rest} (formula : FormulaTokens input value rest) : BodyTokens input (.fof value) rest
  | cnfFalse {opening value closing rest} (openParen : Punct opening '(')
      (falsity : value.kind = .legacy .falsity) (closeParen : Punct closing ')') :
      BodyTokens (opening :: value :: closing :: rest) (.cnf []) rest
  | cnf {opening input values closing rest} (openParen : Punct opening '(')
      (clauses : CnfLiteralsTokens input values (closing :: rest)) (closeParen : Punct closing ')') :
      BodyTokens (opening :: input) (.cnf values) rest

def RecordName (token : Token) (name : Name) : Prop :=
  ∃ kind, token.kind = .legacy kind ∧ kind.name = some name

def BodyKind : Body → String
  | .cnf _ => "cnf"
  | .fof _ => "fof"

def bodyEnd (endOffset : Nat) (input rest : List Token) : Nat :=
  ((input.take (input.length - rest.length)).getLast?.map Token.stop).getD endOffset

inductive DeclarationTokens : List Token → Declaration → List Token → Prop where
  | declaration {keyword opening nameToken name nameComma role roleComma bodyInput body closing dot rest endOffset}
      (keywordKind : keyword.kind = .legacy (.lower (BodyKind body)))
      (openParen : Punct opening '(') (recordName : RecordName nameToken name)
      (commaName : Punct nameComma ',') (axiomRole : role.kind = .legacy (.lower "axiom"))
      (commaRole : Punct roleComma ',')
      (parsed : BodyTokens bodyInput body (closing :: dot :: rest))
      (closeParen : Punct closing ')') (period : Punct dot '.') :
      DeclarationTokens (keyword :: opening :: nameToken :: nameComma :: role :: roleComma :: bodyInput)
        ⟨name, body, keyword.start, dot.stop, offset endOffset bodyInput,
          bodyEnd endOffset bodyInput (closing :: dot :: rest)⟩ rest

inductive StatementsTokens : List Token → List Declaration → Prop where
  | empty : StatementsTokens [] []
  | cons {input first middle rest} (head : DeclarationTokens input first middle)
      (tail : StatementsTokens middle rest) : StatementsTokens input (first :: rest)

def WellNamed (declarations : List Declaration) : Prop :=
  (declarations.map Declaration.name).Nodup

/-- CNF variables are implicitly clause-local. FOF bodies must be closed. -/
def Closed (declarations : List Declaration) : Prop :=
  ∀ declaration ∈ declarations, match declaration.body with
    | .cnf _ => True
    | .fof body => body.Within []

end Fang.TptpCandidate.FullFof.Grammar
