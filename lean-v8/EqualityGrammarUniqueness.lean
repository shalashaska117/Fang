/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Unique named interpretation of the restricted equality CNF token grammar. -/
import EqualitySourceGrammar

namespace Fang.EqualitySource.Grammar
open Source.Grammar (LowerName VariableName)

theorem TermTokens.head {input term rest} (parsed : TermTokens input term rest) :
    ∃ name tail, input = name :: tail ∧ (LowerName name ∨ VariableName name) := by
  cases parsed with
  | variableTerm name rest valid => exact ⟨name, rest, rfl, .inr valid⟩
  | constant name rest valid _ => exact ⟨name, rest, rfl, .inl valid⟩
  | application name valid _ => exact ⟨name, _, rfl, .inl valid⟩

theorem TermTokens.not_head {input term rest text} (parsed : TermTokens input term rest)
    (invalid : ¬ LowerName text ∧ ¬ VariableName text) : input.head? ≠ some text := by
  intro same
  obtain ⟨name, tail, shape, valid⟩ := parsed.head
  simp only [shape, List.head?_cons, Option.some.injEq] at same
  cases same
  exact valid.elim invalid.1 invalid.2

theorem negate_not_name : ¬ LowerName "~" ∧ ¬ VariableName "~" := by
  constructor
  · rintro ⟨first, rest, bytes, firstLower, _⟩
    change ([126] : Source.Grammar.Bytes) = first :: rest at bytes
    have equal := (List.cons.inj bytes).1
    subst first
    simp [Source.Grammar.IsLower] at firstLower
  · rintro ⟨first, rest, bytes, firstUpper, _⟩
    change ([126] : Source.Grammar.Bytes) = first :: rest at bytes
    have equal := (List.cons.inj bytes).1
    subst first
    simp [Source.Grammar.IsUpper] at firstUpper

theorem false_not_name : ¬ LowerName "$false" ∧ ¬ VariableName "$false" := by
  constructor
  · exact Source.Grammar.false_not_lower
  · rintro ⟨first, rest, bytes, firstUpper, _⟩
    change ([36, 102, 97, 108, 115, 101] : Source.Grammar.Bytes) = first :: rest at bytes
    have equal := (List.cons.inj bytes).1
    subst first
    simp [Source.Grammar.IsUpper] at firstUpper

theorem LiteralTokens.unique {input left right leftRest rightRest}
    (first : LiteralTokens input left leftRest) (second : LiteralTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | predicate head stop =>
    cases second with
    | predicate other _ =>
      obtain ⟨same, restSame⟩ := head.unique other
      obtain ⟨rfl, rfl⟩ := Source.Term.app.inj same
      exact ⟨rfl, restSame⟩
    | negative _ => exact False.elim (head.not_head negate_not_name rfl)
    | equal other _ =>
      have restSame := (head.unique other).2
      exact False.elim (stop.1 (by rw [restSame]; rfl))
    | notEqual other _ =>
      have restSame := (head.unique other).2
      exact False.elim (stop.2 (by rw [restSame]; rfl))
  | negative head stop =>
    cases second with
    | predicate other _ => exact False.elim (other.not_head negate_not_name rfl)
    | negative other _ =>
      obtain ⟨same, restSame⟩ := head.unique other
      obtain ⟨rfl, rfl⟩ := Source.Term.app.inj same
      exact ⟨rfl, restSame⟩
    | equal other _ => exact False.elim (other.not_head negate_not_name rfl)
    | notEqual other _ => exact False.elim (other.not_head negate_not_name rfl)
  | equal head tail =>
    cases second with
    | predicate other stop =>
      have restSame := (other.unique head).2
      exact False.elim (stop.1 (by rw [restSame]; rfl))
    | negative _ => exact False.elim (head.not_head negate_not_name rfl)
    | equal other otherTail =>
      obtain ⟨termSame, middleSame⟩ := head.unique other
      have middleSame := (List.cons.inj middleSame).2
      subst middleSame
      obtain ⟨tailSame, restSame⟩ := tail.unique otherTail
      cases termSame; cases tailSame
      exact ⟨rfl, restSame⟩
    | notEqual other _ => have impossible := (head.unique other).2; simp at impossible
  | notEqual head tail =>
    cases second with
    | predicate other stop =>
      have restSame := (other.unique head).2
      exact False.elim (stop.2 (by rw [restSame]; rfl))
    | negative _ => exact False.elim (head.not_head negate_not_name rfl)
    | equal other _ => have impossible := (head.unique other).2; simp at impossible
    | notEqual other otherTail =>
      obtain ⟨termSame, middleSame⟩ := head.unique other
      have middleSame := (List.cons.inj middleSame).2
      subst middleSame
      obtain ⟨tailSame, restSame⟩ := tail.unique otherTail
      cases termSame; cases tailSame
      exact ⟨rfl, restSame⟩

theorem DisjunctionTokens.unique {input left right leftRest rightRest}
    (first : DisjunctionTokens input left leftRest)
    (second : DisjunctionTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction first generalizing right rightRest with
  | last head =>
    cases second with
    | last other =>
      obtain ⟨same, restSame⟩ := head.unique other
      exact ⟨congrArg (fun literal => [literal]) same, (List.cons.inj restSame).2⟩
    | more other _ => have impossible := (head.unique other).2; simp at impossible
  | more head tail ih =>
    cases second with
    | last other => have impossible := (head.unique other).2; simp at impossible
    | more other otherTail =>
      obtain ⟨same, middleSame⟩ := head.unique other
      have middleSame := (List.cons.inj middleSame).2
      subst middleSame
      obtain ⟨tailSame, restSame⟩ := ih otherTail
      cases same; cases tailSame
      exact ⟨rfl, restSame⟩

theorem DisjunctionTokens.not_false {input literals rest}
    (parsed : DisjunctionTokens input literals rest) : input.head? ≠ some "$false" := by
  intro same
  cases parsed with
  | last head | more head _ =>
    cases head with
    | predicate atom _ => exact atom.not_head false_not_name same
    | negative _ _ => simp at same
    | equal first _ | notEqual first _ => exact first.not_head false_not_name same

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

theorem StatementTokens.unique {input left right leftRest rightRest}
    (first : StatementTokens input left leftRest) (second : StatementTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | «axiom» valid body =>
    cases second with
    | «axiom» _ other =>
      obtain ⟨same, restSame⟩ := body.unique other
      cases same
      exact ⟨rfl, (List.cons.inj (List.cons.inj restSame).2).2⟩

theorem ProblemTokens.unique {input left right}
    (first : ProblemTokens input left) (second : ProblemTokens input right) : left = right := by
  induction first generalizing right with
  | nil =>
    cases second with
    | nil => rfl
    | cons head _ => cases head
  | cons head tail ih =>
    cases second with
    | nil => cases head
    | cons other otherTail =>
      obtain ⟨same, restSame⟩ := head.unique other
      cases same; cases restSame
      exact congrArg (List.cons _) (ih otherTail)

end Fang.EqualitySource.Grammar
