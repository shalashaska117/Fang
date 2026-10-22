/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import AnnotationLexer

namespace Fang.TstpBody
open Fang.TstpUnique

theorem read_unique {input first second leftRest rightRest}
    (left : readToken input = some (first, leftRest))
    (right : readToken input = some (second, rightRest)) :
    first = second ∧ leftRest = rightRest :=
  Prod.mk.inj (Option.some.inj (left.symm.trans right))

mutual
inductive TermPrefix : List Char → Source.Term → List Char → Prop where
  | variableTerm {input rest name}
      (read : readToken input = some (.variable name, rest)) :
      TermPrefix input (.var name) rest
  | constant {input rest name}
      (read : readToken input = some (.atom name, rest))
      (noArguments : ∀ tail, readToken rest ≠ some (.punctuation '(', tail)) :
      TermPrefix input (.app name []) rest
  | application {input afterName argumentsStart rest name arguments}
      (read : readToken input = some (.atom name, afterName))
      (opening : readToken afterName = some (.punctuation '(', argumentsStart))
      (children : ArgumentsPrefix argumentsStart arguments rest) :
      TermPrefix input (.app name arguments) rest
inductive ArgumentsPrefix : List Char → List Source.Term → List Char → Prop where
  | last {input afterTerm rest term}
      (head : TermPrefix input term afterTerm)
      (closing : readToken afterTerm = some (.punctuation ')', rest)) :
      ArgumentsPrefix input [term] rest
  | more {input afterTerm middle rest term terms}
      (head : TermPrefix input term afterTerm)
      (comma : readToken afterTerm = some (.punctuation ',', middle))
      (tail : ArgumentsPrefix middle terms rest) :
      ArgumentsPrefix input (term :: terms) rest
end

mutual
theorem TermPrefix.unique {input left right leftRest rightRest}
    (first : TermPrefix input left leftRest) (second : TermPrefix input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | variableTerm read =>
      cases second with
      | variableTerm other =>
          obtain ⟨tokenEqual, restEqual⟩ := read_unique read other
          cases tokenEqual
          exact ⟨rfl, restEqual⟩
      | constant other _ => cases (read_unique read other).1
      | application other _ _ => cases (read_unique read other).1
  | constant read noArguments =>
      cases second with
      | variableTerm other => cases (read_unique read other).1
      | constant other _ =>
          obtain ⟨tokenEqual, restEqual⟩ := read_unique read other
          cases tokenEqual
          exact ⟨rfl, restEqual⟩
      | application other opening _ =>
          obtain ⟨_, restEqual⟩ := read_unique read other
          cases restEqual
          exact False.elim (noArguments _ opening)
  | application read opening children =>
      cases second with
      | variableTerm other => cases (read_unique read other).1
      | constant other noArguments =>
          obtain ⟨_, restEqual⟩ := read_unique read other
          cases restEqual
          exact False.elim (noArguments _ opening)
      | application other otherOpening otherChildren =>
          obtain ⟨tokenEqual, restEqual⟩ := read_unique read other
          cases tokenEqual
          cases restEqual
          have middleEqual := (read_unique opening otherOpening).2
          cases middleEqual
          obtain ⟨termsEqual, suffixEqual⟩ := children.unique otherChildren
          cases termsEqual
          exact ⟨rfl, suffixEqual⟩
theorem ArgumentsPrefix.unique {input left right leftRest rightRest}
    (first : ArgumentsPrefix input left leftRest)
    (second : ArgumentsPrefix input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | last head closing =>
      cases second with
      | last other otherClosing =>
          obtain ⟨termEqual, middleEqual⟩ := head.unique other
          cases middleEqual
          exact ⟨congrArg (fun term => [term]) termEqual,
            (read_unique closing otherClosing).2⟩
      | more other comma _ =>
          have middleEqual := (head.unique other).2
          cases middleEqual
          have impossible := (read_unique closing comma).1
          contradiction
  | more head comma tail =>
      cases second with
      | last other closing =>
          have middleEqual := (head.unique other).2
          cases middleEqual
          have impossible := (read_unique comma closing).1
          contradiction
      | more other otherComma otherTail =>
          obtain ⟨termEqual, middleEqual⟩ := head.unique other
          cases middleEqual
          have suffixEqual := (read_unique comma otherComma).2
          cases suffixEqual
          obtain ⟨termsEqual, restEqual⟩ := tail.unique otherTail
          cases termEqual
          cases termsEqual
          exact ⟨rfl, restEqual⟩
end

theorem TermPrefix.head_kind {input term rest} (parsed : TermPrefix input term rest) :
    ∃ name middle, readToken input = some (.atom name, middle) ∨
      readToken input = some (.variable name, middle) := by
  cases parsed with
  | variableTerm read => exact ⟨_, _, Or.inr read⟩
  | constant read _ => exact ⟨_, _, Or.inl read⟩
  | application read _ _ => exact ⟨_, _, Or.inl read⟩

theorem TermPrefix.not_punctuation {input term rest}
    (parsed : TermPrefix input term rest) (c : Char) (suffix : List Char) :
    readToken input ≠ some (.punctuation c, suffix) := by
  intro read
  obtain ⟨_, _, head | head⟩ := parsed.head_kind <;> cases (read_unique head read).1

theorem TermPrefix.not_false {input term rest}
    (parsed : TermPrefix input term rest) (suffix : List Char) :
    readToken input ≠ some (.falseLiteral, suffix) := by
  intro read
  obtain ⟨_, _, head | head⟩ := parsed.head_kind <;> cases (read_unique head read).1

inductive LiteralPrefix : List Char → Source.Literal → List Char → Prop where
  | positive {input rest name arguments}
      (atom : TermPrefix input (.app name arguments) rest) :
      LiteralPrefix input ⟨true, name, arguments⟩ rest
  | negative {input afterNegation rest name arguments}
      (negation : readToken input = some (.punctuation '~', afterNegation))
      (atom : TermPrefix afterNegation (.app name arguments) rest) :
      LiteralPrefix input ⟨false, name, arguments⟩ rest

theorem LiteralPrefix.unique {input left right leftRest rightRest}
    (first : LiteralPrefix input left leftRest) (second : LiteralPrefix input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | positive atom =>
      cases second with
      | positive other =>
          obtain ⟨equal, restEqual⟩ := atom.unique other
          obtain ⟨nameEqual, argumentsEqual⟩ := Source.Term.app.inj equal
          cases nameEqual; cases argumentsEqual
          exact ⟨rfl, restEqual⟩
      | negative negation _ => exact False.elim (atom.not_punctuation _ _ negation)
  | negative negation atom =>
      cases second with
      | positive other => exact False.elim (other.not_punctuation _ _ negation)
      | negative otherNegation other =>
          have middleEqual := (read_unique negation otherNegation).2
          cases middleEqual
          obtain ⟨equal, restEqual⟩ := atom.unique other
          obtain ⟨nameEqual, argumentsEqual⟩ := Source.Term.app.inj equal
          cases nameEqual; cases argumentsEqual
          exact ⟨rfl, restEqual⟩

theorem LiteralPrefix.not_false {input literal rest}
    (parsed : LiteralPrefix input literal rest) (suffix : List Char) :
    readToken input ≠ some (.falseLiteral, suffix) := by
  intro read
  cases parsed with
  | positive atom => exact atom.not_false _ read
  | negative negation _ => cases (read_unique negation read).1

inductive DisjunctionPrefix : List Char → List Source.Literal → List Char → Prop where
  | last {input afterLiteral rest literal}
      (head : LiteralPrefix input literal afterLiteral)
      (closing : readToken afterLiteral = some (.punctuation ')', rest)) :
      DisjunctionPrefix input [literal] rest
  | more {input afterLiteral middle rest literal literals}
      (head : LiteralPrefix input literal afterLiteral)
      (disjoin : readToken afterLiteral = some (.punctuation '|', middle))
      (tail : DisjunctionPrefix middle literals rest) :
      DisjunctionPrefix input (literal :: literals) rest

theorem DisjunctionPrefix.unique {input left right leftRest rightRest}
    (first : DisjunctionPrefix input left leftRest)
    (second : DisjunctionPrefix input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction first generalizing right rightRest with
  | last head closing =>
      cases second with
      | last other otherClosing =>
          obtain ⟨literalEqual, middleEqual⟩ := head.unique other
          cases middleEqual
          exact ⟨congrArg (fun literal => [literal]) literalEqual,
            (read_unique closing otherClosing).2⟩
      | more other disjoin _ =>
          have middleEqual := (head.unique other).2
          cases middleEqual
          have impossible := (read_unique closing disjoin).1
          contradiction
  | more head disjoin tail ih =>
      cases second with
      | last other closing =>
          have middleEqual := (head.unique other).2
          cases middleEqual
          have impossible := (read_unique disjoin closing).1
          contradiction
      | more other otherDisjoin otherTail =>
          obtain ⟨literalEqual, middleEqual⟩ := head.unique other
          cases middleEqual
          have suffixEqual := (read_unique disjoin otherDisjoin).2
          cases suffixEqual
          obtain ⟨literalsEqual, restEqual⟩ := ih otherTail
          cases literalEqual
          cases literalsEqual
          exact ⟨rfl, restEqual⟩

theorem DisjunctionPrefix.not_false {input literals rest}
    (parsed : DisjunctionPrefix input literals rest) (suffix : List Char) :
    readToken input ≠ some (.falseLiteral, suffix) := by
  cases parsed with
  | last head _ | more head _ _ => exact head.not_false suffix

inductive BodyPrefix : List Char → List Source.Literal → List Char → Prop where
  | falsity {input afterFalse rest}
      (read : readToken input = some (.falseLiteral, afterFalse))
      (closing : readToken afterFalse = some (.punctuation ')', rest)) :
      BodyPrefix input [] rest
  | disjunction {input literals rest} (body : DisjunctionPrefix input literals rest) :
      BodyPrefix input literals rest

theorem BodyPrefix.unique {input left right leftRest rightRest}
    (first : BodyPrefix input left leftRest) (second : BodyPrefix input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | falsity read closing =>
      cases second with
      | falsity other otherClosing =>
          have middleEqual := (read_unique read other).2
          cases middleEqual
          exact ⟨rfl, (read_unique closing otherClosing).2⟩
      | disjunction other => exact False.elim (other.not_false _ read)
  | disjunction body =>
      cases second with
      | falsity read _ => exact False.elim (body.not_false _ read)
      | disjunction other => exact body.unique other

end Fang.TstpBody
