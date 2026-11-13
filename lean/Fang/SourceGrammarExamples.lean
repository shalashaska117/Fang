/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

Checked token-grammar witnesses. Byte-to-token correspondence remains open.
-/
import Fang.SourceGrammar
import Fang.SourceExamples

namespace Fang.Source.Grammar.Examples

def documentedTokens : List Token := [
  .lower "cnf", .lparen, .lower "c0", .comma, .lower "axiom", .comma, .lparen,
  .lower "p", .lparen, .variable "X", .rparen, .disjoin,
  .lower "p", .lparen, .variable "Y", .rparen, .disjoin,
  .lower "p", .lparen, .variable "X", .rparen, .rparen, .rparen, .period,
  .lower "cnf", .lparen, .lower "c1", .comma, .lower "axiom", .comma, .lparen,
  .negate, .lower "p", .lparen, .lower "a", .rparen, .rparen, .rparen, .period]

theorem documented_parse : ProblemTokens documentedTokens Source.Examples.problem := by
  exact .statement (.statement "c0" (.disjunction
    (.more (.positive (.application "p" (.last (.variableTerm "X" _))))
      (.more (.positive (.application "p" (.last (.variableTerm "Y" _))))
        (.last (.positive (.application "p" (.last (.variableTerm "X" _)))))))))
    (.statement (.statement "c1" (.disjunction
      (.last (.negative (.application "p" (.last (.constant "a" _ (by decide)))))))) .empty)

theorem only_documented_parse {problem : Problem}
    (parsed : ProblemTokens documentedTokens problem) : problem = Source.Examples.problem :=
  parsed.unique documented_parse

theorem no_empty_arguments {term rest} :
    ¬ TermTokens [.lower "a", .lparen, .rparen] term rest := by
  intro parsed
  cases parsed with
  | constant _ _ noArguments => exact noArguments rfl
  | application _ children =>
      cases children with
      | last head | more head _ => cases head

theorem no_trailing_tokens {problem} :
    ¬ ProblemTokens [.period] problem := by
  intro parsed
  cases parsed with
  | statement head _ => cases head

#print axioms documented_parse
#print axioms only_documented_parse

end Fang.Source.Grammar.Examples
