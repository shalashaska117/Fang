/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel controls for the rewriting pass: one per rule, with the exact rewritten formula, and the shape of the
   injectivity axiom of MSC014+1, where the pass moves the inner block of universal quantifiers under the
   implication. -/
import ModelRewrite

namespace Fang.TptpCandidate.FullFof.Model.RewriteControls
open Fang.TptpCandidate.FullFof.Model

set_option maxRecDepth 100000
set_option cbv.maxSteps 2000000

/-- An atom over variables. -/
private def atom (name : String) (variables : List String) : Formula :=
  .atom name (variables.map Source.Term.var)

private def conj (left right : Formula) : Formula := .pair .conj left right
private def disj (left right : Formula) : Formula := .pair .disj left right
private def implies (left right : Formula) : Formula := .pair .implies left right

/-- Two quantifiers of one kind are swapped when the outer one moves inward. -/
theorem rewrite_swap_all :
    rewrite (.all "X" (.all "Y" (atom "p" ["X", "Y"]))) = .all "Y" (.all "X" (atom "p" ["X", "Y"])) := by
  cbv

theorem rewrite_swap_ex :
    rewrite (.ex "X" (.ex "Y" (atom "p" ["X", "Y"]))) = .ex "Y" (.ex "X" (atom "p" ["X", "Y"])) := by
  cbv

/-- `∀` distributes over `&`, `∃` over `|`. -/
theorem rewrite_all_conj :
    rewrite (.all "X" (conj (atom "p" ["X"]) (atom "q" ["X"]))) =
      conj (.all "X" (atom "p" ["X"])) (.all "X" (atom "q" ["X"])) := by
  cbv

theorem rewrite_ex_disj :
    rewrite (.ex "X" (disj (atom "p" ["X"]) (atom "q" ["X"]))) =
      disj (.ex "X" (atom "p" ["X"])) (.ex "X" (atom "q" ["X"])) := by
  cbv

/-- A quantifier moves past a side that does not use its variable. -/
theorem rewrite_all_disj_right :
    rewrite (.all "X" (disj (atom "p" ["X"]) (atom "q" []))) = disj (.all "X" (atom "p" ["X"])) (atom "q" []) := by
  cbv

theorem rewrite_all_disj_left :
    rewrite (.all "X" (disj (atom "q" []) (atom "p" ["X"]))) = disj (atom "q" []) (.all "X" (atom "p" ["X"])) := by
  cbv

theorem rewrite_ex_conj_right :
    rewrite (.ex "X" (conj (atom "p" ["X"]) (atom "q" []))) = conj (.ex "X" (atom "p" ["X"])) (atom "q" []) := by
  cbv

/-- Past an antecedent that does not use the variable; into an antecedent as `∃`. -/
theorem rewrite_all_implies_antecedent :
    rewrite (.all "X" (implies (atom "q" []) (atom "p" ["X"]))) =
      implies (atom "q" []) (.all "X" (atom "p" ["X"])) := by
  cbv

theorem rewrite_all_implies_consequent :
    rewrite (.all "X" (implies (atom "p" ["X"]) (atom "q" []))) =
      implies (.ex "X" (atom "p" ["X"])) (atom "q" []) := by
  cbv

/-- `∃ X, (A => B)` is `(∀ X, A) => ∃ X, B`. -/
theorem rewrite_ex_implies :
    rewrite (.ex "X" (implies (atom "p" ["X"]) (atom "q" ["X"]))) =
      implies (.all "X" (atom "p" ["X"])) (.ex "X" (atom "q" ["X"])) := by
  cbv

/-- `B <= A` with `A` free of the variable: the quantifier moves into `B`. -/
theorem rewrite_all_reverse :
    rewrite (.all "X" (.pair .reverse (atom "p" ["X"]) (atom "q" []))) =
      .pair .reverse (.all "X" (atom "p" ["X"])) (atom "q" []) := by
  cbv

/-- Through `~|` and `~&` as the dual quantifier. -/
theorem rewrite_all_nor :
    rewrite (.all "X" (.pair .nor (atom "p" ["X"]) (atom "q" ["X"]))) =
      .pair .nor (.ex "X" (atom "p" ["X"])) (.ex "X" (atom "q" ["X"])) := by
  cbv

theorem rewrite_ex_nand :
    rewrite (.ex "X" (.pair .nand (atom "p" ["X"]) (atom "q" ["X"]))) =
      .pair .nand (.all "X" (atom "p" ["X"])) (.all "X" (atom "q" ["X"])) := by
  cbv

/-- Through negation as the dual quantifier. -/
theorem rewrite_all_neg : rewrite (.all "X" (.neg (atom "p" ["X"]))) = .neg (.ex "X" (atom "p" ["X"])) := by
  cbv

/-- A quantifier whose variable does not occur is dropped. -/
theorem rewrite_vacuous : rewrite (.all "X" (atom "q" [])) = atom "q" [] := by
  cbv

/-- A conjunctive antecedent is curried. -/
theorem rewrite_curry :
    rewrite (implies (conj (atom "p" []) (atom "q" [])) (atom "r" [])) =
      implies (atom "p" []) (implies (atom "q" []) (atom "r" [])) := by
  cbv

/-- Connectives without a rule keep the quantifier above them. -/
theorem rewrite_all_iff :
    rewrite (.all "X" (.pair .iff (atom "p" ["X"]) (atom "q" []))) =
      .all "X" (.pair .iff (atom "p" ["X"]) (atom "q" [])) := by
  cbv

/-- The injectivity shape `! [X,Y,Z] : ((f(X,Z) & f(Y,Z)) => e(X,Y))`: the block over `Y` ends up under the
    implication, so it is evaluated only where `f(X,Z)` holds. -/
theorem rewrite_injectivity :
    rewrite (.all "X" (.all "Y" (.all "Z"
        (implies (conj (atom "f" ["X", "Z"]) (atom "f" ["Y", "Z"])) (atom "e" ["X", "Y"]))))) =
      .all "Z" (.all "X" (implies (atom "f" ["X", "Z"])
        (.all "Y" (implies (atom "f" ["Y", "Z"]) (atom "e" ["X", "Y"]))))) := by
  cbv

end Fang.TptpCandidate.FullFof.Model.RewriteControls
