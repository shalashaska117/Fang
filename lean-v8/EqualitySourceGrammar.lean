/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Declarative equality source grammar, independent of the executable parser.
   Term relations and uniqueness adapted from Fang's accepted raw FOF grammar. -/
import EqualityNamedSource
import Fang.SourceLexing

namespace Fang.EqualitySource.Grammar
open Source.Grammar (LowerName VariableName name_kinds_disjoint)

mutual
inductive TermTokens : List String → Source.Term → List String → Prop where
  | variableTerm (name : String) (rest : List String) (valid : VariableName name) :
      TermTokens (name :: rest) (.var name) rest
  | constant (name : String) (rest : List String) (valid : LowerName name)
      (noArguments : rest.head? ≠ some "(") :
      TermTokens (name :: rest) (.app name []) rest
  | application (name : String) {input rest arguments} (valid : LowerName name)
      (children : ArgumentsTokens input arguments rest) :
      TermTokens (name :: "(" :: input) (.app name arguments) rest
inductive ArgumentsTokens : List String → List Source.Term → List String → Prop where
  | last {input rest term} (head : TermTokens input term (")" :: rest)) :
      ArgumentsTokens input [term] rest
  | more {input middle rest term terms} (head : TermTokens input term ("," :: middle))
      (tail : ArgumentsTokens middle terms rest) : ArgumentsTokens input (term :: terms) rest
end

/-- A nonempty argument prefix leaves its closing delimiter to the caller. -/
inductive TermsPrefix : List String → List Source.Term → List String → Prop where
  | last {input rest term} (head : TermTokens input term rest)
      (noComma : rest.head? ≠ some ",") : TermsPrefix input [term] rest
  | more {input middle rest term terms} (head : TermTokens input term ("," :: middle))
      (tail : TermsPrefix middle terms rest) : TermsPrefix input (term :: terms) rest

theorem TermsPrefix.arguments {input terms rest}
    (parsed : TermsPrefix input terms (")" :: rest)) : ArgumentsTokens input terms rest := by
  generalize ending : ")" :: rest = output at parsed
  induction parsed with
  | last head noComma => exact .last (ending ▸ head)
  | more head tail ih => exact .more head (ih ending)


mutual
theorem TermTokens.unique {input left right leftRest rightRest}
    (first : TermTokens input left leftRest) (second : TermTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | variableTerm name rest valid =>
      cases second with
      | variableTerm => exact ⟨rfl, rfl⟩
      | constant _ _ lower _ => exact False.elim (name_kinds_disjoint lower valid)
      | application _ lower _ => exact False.elim (name_kinds_disjoint lower valid)
  | constant name rest valid noArguments =>
      cases second with
      | variableTerm _ _ upper => exact False.elim (name_kinds_disjoint valid upper)
      | constant => exact ⟨rfl, rfl⟩
      | application => exact False.elim (noArguments rfl)
  | application name valid children =>
      cases second with
      | variableTerm _ _ upper => exact False.elim (name_kinds_disjoint valid upper)
      | constant _ _ _ noArguments => exact False.elim (noArguments rfl)
      | application _ _ other =>
          obtain ⟨termsEqual, restEqual⟩ := children.unique other
          exact ⟨congrArg (Source.Term.app name) termsEqual, restEqual⟩

theorem ArgumentsTokens.unique {input left right leftRest rightRest}
    (first : ArgumentsTokens input left leftRest)
    (second : ArgumentsTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | last head =>
      cases second with
      | last other =>
          obtain ⟨termEqual, restEqual⟩ := head.unique other
          exact ⟨congrArg (fun term => [term]) termEqual, (List.cons.inj restEqual).2⟩
      | more other tail =>
          have impossible := (head.unique other).2
          simp at impossible
  | more head tail =>
      cases second with
      | last other =>
          have impossible := (head.unique other).2
          simp at impossible
      | more other otherTail =>
          obtain ⟨termEqual, middleEqual⟩ := head.unique other
          have middleEqual := (List.cons.inj middleEqual).2
          subst middleEqual
          obtain ⟨termsEqual, restEqual⟩ := tail.unique otherTail
          cases termEqual; cases termsEqual
          exact ⟨rfl, restEqual⟩
end


/-- Predicate syntax stops before an infix equality operator. -/
def PredicateEnd (rest : List String) : Prop :=
  rest.head? ≠ some "=" ∧ rest.head? ≠ some "!="

inductive LiteralTokens : List String → Literal → List String → Prop where
  | predicate {input rest name arguments}
      (head : TermTokens input (.app name arguments) rest) (stop : PredicateEnd rest) :
      LiteralTokens input ⟨true, .predicate name arguments⟩ rest
  | negative {input rest name arguments}
      (head : TermTokens input (.app name arguments) rest) (stop : PredicateEnd rest) :
      LiteralTokens ("~" :: input) ⟨false, .predicate name arguments⟩ rest
  | equal {input middle rest left right}
      (first : TermTokens input left ("=" :: middle))
      (second : TermTokens middle right rest) :
      LiteralTokens input ⟨true, .equal left right⟩ rest
  | notEqual {input middle rest left right}
      (first : TermTokens input left ("!=" :: middle))
      (second : TermTokens middle right rest) :
      LiteralTokens input ⟨false, .equal left right⟩ rest

inductive DisjunctionPrefix : List String → List Literal → List String → Prop where
  | last {input rest literal} (head : LiteralTokens input literal rest)
      (noDisjoin : rest.head? ≠ some "|") : DisjunctionPrefix input [literal] rest
  | more {input middle rest literal literals} (head : LiteralTokens input literal ("|" :: middle))
      (tail : DisjunctionPrefix middle literals rest) :
      DisjunctionPrefix input (literal :: literals) rest

inductive DisjunctionTokens : List String → List Literal → List String → Prop where
  | last {input rest literal} (head : LiteralTokens input literal (")" :: rest)) :
      DisjunctionTokens input [literal] rest
  | more {input middle rest literal literals} (head : LiteralTokens input literal ("|" :: middle))
      (tail : DisjunctionTokens middle literals rest) :
      DisjunctionTokens input (literal :: literals) rest

theorem DisjunctionPrefix.body {input literals rest}
    (parsed : DisjunctionPrefix input literals (")" :: rest)) : DisjunctionTokens input literals rest := by
  generalize ending : ")" :: rest = output at parsed
  induction parsed with
  | last head noDisjoin => exact .last (ending ▸ head)
  | more head tail ih => exact .more head (ih ending)

inductive BodyTokens : List String → List Literal → List String → Prop where
  | falsity (rest) : BodyTokens ("$false" :: ")" :: rest) [] rest
  | disjunction {input literals rest} (body : DisjunctionTokens input literals rest) :
      BodyTokens input literals rest

inductive StatementTokens : List String → Clause → List String → Prop where
  | axiom {name input rest literals} (valid : LowerName name)
      (body : BodyTokens input literals (")" :: "." :: rest)) :
      StatementTokens ("cnf" :: "(" :: name :: "," :: "axiom" :: "," :: "(" :: input)
        ⟨name, literals⟩ rest

inductive ProblemTokens : List String → Problem → Prop where
  | nil : ProblemTokens [] []
  | cons {input middle clause clauses}
      (first : StatementTokens input clause middle) (rest : ProblemTokens middle clauses) :
      ProblemTokens input (clause :: clauses)

end Fang.EqualitySource.Grammar
