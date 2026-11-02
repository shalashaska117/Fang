/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFCNFGrammar

namespace Fang.FOFGrammar
open Source.Grammar (LowerName VariableName name_kinds_disjoint false_not_lower)

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

theorem TermTokens.app_head {input name args rest}
    (parsed : TermTokens input (.app name args) rest) :
    ∃ tail, input = name :: tail ∧ LowerName name := by
  cases parsed with
  | constant name rest valid noArguments => exact ⟨rest, rfl, valid⟩
  | application name valid children => exact ⟨_, rfl, valid⟩

theorem TermTokens.app_not_head {input name args rest text}
    (parsed : TermTokens input (.app name args) rest) (invalid : ¬ LowerName text) :
    input.head? ≠ some text := by
  intro same
  obtain ⟨tail, shape, valid⟩ := parsed.app_head
  simp only [shape, List.head?_cons, Option.some.injEq] at same
  exact invalid (same ▸ valid)

theorem negate_not_lower : ¬ LowerName "~" := by
  rintro ⟨first, rest, bytes, firstLower, _⟩
  change ([126] : Source.Grammar.Bytes) = first :: rest at bytes
  have equal := (List.cons.inj bytes).1
  subst first
  simp [Source.Grammar.IsLower] at firstLower

theorem LiteralTokens.unique {input left right leftRest rightRest}
    (first : LiteralTokens input left leftRest) (second : LiteralTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | positive atom =>
      cases second with
      | positive other =>
          obtain ⟨equal, restEqual⟩ := atom.unique other
          obtain ⟨nameEqual, argumentsEqual⟩ := Source.Term.app.inj equal
          cases nameEqual; cases argumentsEqual
          exact ⟨rfl, restEqual⟩
      | negative other => exact False.elim (atom.app_not_head negate_not_lower rfl)
  | negative atom =>
      cases second with
      | positive other => exact False.elim (other.app_not_head negate_not_lower rfl)
      | negative other =>
          obtain ⟨equal, restEqual⟩ := atom.unique other
          obtain ⟨nameEqual, argumentsEqual⟩ := Source.Term.app.inj equal
          cases nameEqual; cases argumentsEqual
          exact ⟨rfl, restEqual⟩

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
      | more other _ =>
          have impossible := (head.unique other).2
          simp at impossible
  | more head tail ih =>
      cases second with
      | last other =>
          have impossible := (head.unique other).2
          simp at impossible
      | more other otherTail =>
          obtain ⟨equal, middleEqual⟩ := head.unique other
          have middleEqual := (List.cons.inj middleEqual).2
          subst middleEqual
          obtain ⟨tailEqual, restEqual⟩ := ih otherTail
          cases equal; cases tailEqual
          exact ⟨rfl, restEqual⟩

theorem DisjunctionTokens.not_false {input literals rest}
    (parsed : DisjunctionTokens input literals rest) : input.head? ≠ some "$false" := by
  intro same
  cases parsed with
  | last head | more head _ =>
      cases head with
      | positive atom => exact atom.app_not_head false_not_lower same
      | negative atom => simp at same

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

theorem CNFDeclarationTokens.unique {input left right leftRest rightRest}
    (first : CNFDeclarationTokens input left leftRest)
    (second : CNFDeclarationTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | «axiom» valid body =>
      cases second with
      | «axiom» otherValid other =>
          obtain ⟨equal, restEqual⟩ := body.unique other
          cases equal
          exact ⟨rfl, (List.cons.inj (List.cons.inj restEqual).2).2⟩

end Fang.FOFGrammar
