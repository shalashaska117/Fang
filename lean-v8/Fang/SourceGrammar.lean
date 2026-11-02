/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

Declarative token grammar, independent of the executable frontend.
Token spelling and byte-to-token correspondence are separate obligations.
-/
import Fang.SourceSemantics

namespace Fang.Source.Grammar

inductive Token where
  | lower : String → Token
  | variable : String → Token
  | lparen | rparen | comma | period | disjoin | negate | falseLiteral
  deriving DecidableEq, Repr

mutual
inductive TermTokens : List Token → Term → List Token → Prop where
  | variableTerm (name : String) (rest : List Token) :
      TermTokens (.variable name :: rest) (.var name) rest
  | constant (name : String) (rest : List Token)
      (noArguments : rest.head? ≠ some .lparen) :
      TermTokens (.lower name :: rest) (.app name []) rest
  | application (name : String) {input rest : List Token} {arguments : List Term}
      (children : ArgumentsTokens input arguments rest) :
      TermTokens (.lower name :: .lparen :: input) (.app name arguments) rest
inductive ArgumentsTokens : List Token → List Term → List Token → Prop where
  | last {input rest : List Token} {term : Term}
      (head : TermTokens input term (.rparen :: rest)) :
      ArgumentsTokens input [term] rest
  | more {input middle rest : List Token} {term : Term} {terms : List Term}
      (head : TermTokens input term (.comma :: middle))
      (tail : ArgumentsTokens middle terms rest) :
      ArgumentsTokens input (term :: terms) rest
end

mutual
theorem TermTokens.unique {input left right leftRest rightRest}
    (first : TermTokens input left leftRest) (second : TermTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | variableTerm name rest => cases second; exact ⟨rfl, rfl⟩
  | constant name rest noArguments =>
      cases second with
      | constant => exact ⟨rfl, rfl⟩
      | application children => exact False.elim (noArguments rfl)
  | application name children =>
      cases second with
      | constant _ _ noArguments => exact False.elim (noArguments rfl)
      | application _ other =>
          obtain ⟨termsEqual, restEqual⟩ := children.unique other
          exact ⟨congrArg (Term.app name) termsEqual, restEqual⟩
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
          cases impossible
  | more head tail =>
      cases second with
      | last other =>
          have impossible := (head.unique other).2
          cases impossible
      | more other otherTail =>
          obtain ⟨termEqual, middleEqual⟩ := head.unique other
          have middleEqual := (List.cons.inj middleEqual).2
          subst middleEqual
          obtain ⟨termsEqual, restEqual⟩ := tail.unique otherTail
          cases termEqual
          cases termsEqual
          exact ⟨rfl, restEqual⟩
end

theorem ArgumentsTokens.nonempty {input arguments rest}
    (parsed : ArgumentsTokens input arguments rest) : arguments ≠ [] := by
  cases parsed <;> simp

inductive LiteralTokens : List Token → Literal → List Token → Prop where
  | positive {input rest name arguments}
      (atom : TermTokens input (.app name arguments) rest) :
      LiteralTokens input ⟨true, name, arguments⟩ rest
  | negative {input rest name arguments}
      (atom : TermTokens input (.app name arguments) rest) :
      LiteralTokens (.negate :: input) ⟨false, name, arguments⟩ rest

theorem LiteralTokens.unique {input left right leftRest rightRest}
    (first : LiteralTokens input left leftRest) (second : LiteralTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | positive atom =>
      cases second with
      | positive other =>
          obtain ⟨equal, restEqual⟩ := atom.unique other
          obtain ⟨nameEqual, argumentsEqual⟩ := Term.app.inj equal
          cases nameEqual; cases argumentsEqual
          exact ⟨rfl, restEqual⟩
      | negative other => cases atom
  | negative atom =>
      cases second with
      | positive other => cases other
      | negative other =>
          obtain ⟨equal, restEqual⟩ := atom.unique other
          obtain ⟨nameEqual, argumentsEqual⟩ := Term.app.inj equal
          cases nameEqual; cases argumentsEqual
          exact ⟨rfl, restEqual⟩

inductive DisjunctionTokens : List Token → List Literal → List Token → Prop where
  | last {input rest literal}
      (head : LiteralTokens input literal (.rparen :: rest)) :
      DisjunctionTokens input [literal] rest
  | more {input middle rest literal literals}
      (head : LiteralTokens input literal (.disjoin :: middle))
      (tail : DisjunctionTokens middle literals rest) :
      DisjunctionTokens input (literal :: literals) rest

theorem DisjunctionTokens.unique {input left right leftRest rightRest}
    (first : DisjunctionTokens input left leftRest)
    (second : DisjunctionTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction first generalizing right rightRest with
  | last head =>
      cases second with
      | last other =>
          obtain ⟨equal, restEqual⟩ := head.unique other
          exact ⟨congrArg (fun literal => [literal]) equal, (List.cons.inj restEqual).2⟩
      | more other _ => cases (head.unique other).2
  | more head tail induction =>
      cases second with
      | last other => cases (head.unique other).2
      | more other otherTail =>
          obtain ⟨equal, middleEqual⟩ := head.unique other
          have middleEqual := (List.cons.inj middleEqual).2
          subst middleEqual
          obtain ⟨tailEqual, restEqual⟩ := induction otherTail
          cases equal; cases tailEqual
          exact ⟨rfl, restEqual⟩

theorem DisjunctionTokens.not_false {input literals rest}
    (parsed : DisjunctionTokens input literals rest) : input.head? ≠ some .falseLiteral := by
  intro equal
  cases parsed with
  | last head | more head _ =>
      cases head with
      | positive atom => cases atom <;> cases equal
      | negative atom => cases equal

inductive BodyTokens : List Token → List Literal → List Token → Prop where
  | falsity (rest : List Token) : BodyTokens (.falseLiteral :: .rparen :: rest) [] rest
  | disjunction {input literals rest} (body : DisjunctionTokens input literals rest) :
      BodyTokens input literals rest

theorem BodyTokens.unique {input left right leftRest rightRest}
    (first : BodyTokens input left leftRest) (second : BodyTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | falsity rest =>
      cases second with
      | falsity => exact ⟨rfl, rfl⟩
      | disjunction other => exact False.elim (other.not_false rfl)
  | disjunction body =>
      cases second with
      | falsity => exact False.elim (body.not_false rfl)
      | disjunction other => exact body.unique other

inductive StatementTokens : List Token → Clause → List Token → Prop where
  | statement (name : String) {input literals rest}
      (body : BodyTokens input literals (.rparen :: .period :: rest)) :
      StatementTokens (.lower "cnf" :: .lparen :: .lower name :: .comma ::
        .lower "axiom" :: .comma :: .lparen :: input) ⟨name, literals⟩ rest

theorem StatementTokens.unique {input left right leftRest rightRest}
    (first : StatementTokens input left leftRest)
    (second : StatementTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | statement name body =>
      cases second with
      | statement _ other =>
          obtain ⟨equal, restEqual⟩ := body.unique other
          cases equal
          exact ⟨rfl, (List.cons.inj (List.cons.inj restEqual).2).2⟩

inductive ProblemTokens : List Token → Problem → Prop where
  | empty : ProblemTokens [] []
  | statement {input first middle rest}
      (head : StatementTokens input first middle) (tail : ProblemTokens middle rest) :
      ProblemTokens input (first :: rest)

theorem ProblemTokens.unique {input left right}
    (first : ProblemTokens input left) (second : ProblemTokens input right) : left = right := by
  induction first generalizing right with
  | empty =>
      cases second with
      | empty => rfl
      | statement head _ => cases head
  | statement head tail induction =>
      cases second with
      | empty => cases head
      | statement other otherTail =>
          obtain ⟨equal, middleEqual⟩ := head.unique other
          subst middleEqual
          have tailEqual := induction otherTail
          cases equal; cases tailEqual
          rfl

#print axioms TermTokens.unique
#print axioms ProblemTokens.unique

end Fang.Source.Grammar
