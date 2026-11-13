/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Token consumption bounds for the independent source grammar. These bounds do
not by themselves prove that the executable parser has sufficient fuel.
-/
import Fang.SourceGrammar

namespace Fang.Source.Grammar

mutual
theorem TermTokens.consumes {input term rest}
    (parsed : TermTokens input term rest) : rest.length < input.length := by
  cases parsed with
  | variableTerm => simp
  | constant => simp
  | application name children =>
      have shorter := children.consumes
      simp only [List.length_cons]
      omega

theorem ArgumentsTokens.consumes {input terms rest}
    (parsed : ArgumentsTokens input terms rest) : rest.length + 1 < input.length := by
  cases parsed with
  | last head => simpa using head.consumes
  | more head tail =>
      have first := head.consumes
      have second := tail.consumes
      simp only [List.length_cons] at first
      omega
end

theorem LiteralTokens.consumes {input literal rest}
    (parsed : LiteralTokens input literal rest) : rest.length < input.length := by
  cases parsed with
  | positive atom => exact atom.consumes
  | negative atom =>
      have shorter := atom.consumes
      simp only [List.length_cons]
      omega

theorem DisjunctionTokens.consumes {input literals rest}
    (parsed : DisjunctionTokens input literals rest) : rest.length + 1 < input.length := by
  induction parsed with
  | last head => simpa using head.consumes
  | more head tail induction =>
      have first := head.consumes
      simp only [List.length_cons] at first
      omega

theorem BodyTokens.consumes {input literals rest}
    (parsed : BodyTokens input literals rest) : rest.length + 1 < input.length := by
  cases parsed with
  | falsity => simp
  | disjunction body => exact body.consumes

theorem StatementTokens.consumes {input clause rest}
    (parsed : StatementTokens input clause rest) : rest.length + 11 ≤ input.length := by
  cases parsed with
  | statement name body =>
      have shorter := body.consumes
      simp only [List.length_cons] at shorter ⊢
      omega

theorem ProblemTokens.clause_count_bound {input problem}
    (parsed : ProblemTokens input problem) : 11 * problem.length ≤ input.length := by
  induction parsed with
  | empty => simp
  | statement head tail induction =>
      have shorter := head.consumes
      simp only [List.length_cons]
      omega

#print axioms TermTokens.consumes
#print axioms ArgumentsTokens.consumes
#print axioms StatementTokens.consumes
#print axioms ProblemTokens.clause_count_bound

end Fang.Source.Grammar
