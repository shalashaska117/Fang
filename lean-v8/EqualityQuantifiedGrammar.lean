/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent mixed CNF/quantified equality token grammar. -/
import EqualityQuantifiedInput
import EqualitySourceGrammar

namespace Fang.NamedQuantifiedEquality.Grammar
open Source.Grammar (LowerName VariableName)
open EqualitySource.Grammar (TermTokens PredicateEnd)

inductive AtomTokens : List String → Formula → List String → Prop where
  | predicate {input rest name arguments}
      (head : TermTokens input (.app name arguments) rest) (stop : PredicateEnd rest) :
      AtomTokens input (.atom (.predicate name arguments)) rest
  | equal {input middle rest left right}
      (first : TermTokens input left ("=" :: middle)) (second : TermTokens middle right rest) :
      AtomTokens input (.atom (.equal left right)) rest
  | notEqual {input middle rest left right}
      (first : TermTokens input left ("!=" :: middle)) (second : TermTokens middle right rest) :
      AtomTokens input (.neg (.atom (.equal left right))) rest

inductive BindersTokens : List String → List String → List String → Prop where
  | last {name rest} (valid : VariableName name) : BindersTokens (name :: "]" :: rest) [name] rest
  | more {name input names rest} (valid : VariableName name) (tail : BindersTokens input names rest) :
      BindersTokens (name :: "," :: input) (name :: names) rest

inductive FormulaTokens : List String → Formula → List String → Prop where
  | atom {input value rest} (parsed : AtomTokens input value rest) : FormulaTokens input value rest
  | truth (rest) : FormulaTokens ("$true" :: rest) .truth rest
  | falsity (rest) : FormulaTokens ("$false" :: rest) .falsity rest
  | neg {input rest body} (child : FormulaTokens input body rest) :
      FormulaTokens ("~" :: input) (.neg body) rest
  | paren {input rest body} (child : FormulaTokens input body (")" :: rest)) :
      FormulaTokens ("(" :: input) body rest
  | conj {input middle rest left right} (first : FormulaTokens input left ("&" :: middle))
      (second : FormulaTokens middle right (")" :: rest)) :
      FormulaTokens ("(" :: input) (.conj left right) rest
  | disj {input middle rest left right} (first : FormulaTokens input left ("|" :: middle))
      (second : FormulaTokens middle right (")" :: rest)) :
      FormulaTokens ("(" :: input) (.disj left right) rest
  | implies {input middle rest left right} (first : FormulaTokens input left ("=>" :: middle))
      (second : FormulaTokens middle right (")" :: rest)) :
      FormulaTokens ("(" :: input) (.implies left right) rest
  | all {input bodyInput names body rest} (binders : BindersTokens input names (":" :: bodyInput))
      (child : FormulaTokens bodyInput body rest) :
      FormulaTokens ("!" :: "[" :: input) (body.bind true names) rest
  | ex {input bodyInput names body rest} (binders : BindersTokens input names (":" :: bodyInput))
      (child : FormulaTokens bodyInput body rest) :
      FormulaTokens ("?" :: "[" :: input) (body.bind false names) rest

inductive DeclarationTokens : List String → Declaration → List String → Prop where
  | cnf {input clause rest} (parsed : EqualitySource.Grammar.StatementTokens input clause rest) :
      DeclarationTokens input (.cnf clause) rest
  | fof {name input rest body} (valid : LowerName name)
      (parsed : FormulaTokens input body (")" :: "." :: rest)) (closed : body.Within []) :
      DeclarationTokens ("fof" :: "(" :: name :: "," :: "axiom" :: "," :: input) (.fof name body) rest

inductive DeclarationsTokens : List String → List Declaration → Prop where
  | nil : DeclarationsTokens [] []
  | cons {input middle first rest} (head : DeclarationTokens input first middle)
      (tail : DeclarationsTokens middle rest) : DeclarationsTokens input (first :: rest)

def ParsesTokens (input : List String) (declarations : List Declaration) : Prop :=
  DeclarationsTokens input declarations ∧ (declarations.map Declaration.name).Nodup

end Fang.NamedQuantifiedEquality.Grammar
