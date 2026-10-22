/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

Kernel-reduced examples concern these explicit problem ASTs. The source-byte
parser is a separate proof obligation.
-/
import Fang.Checker

namespace Fang.Examples

def p (t : Term) : Literal := ⟨true, ⟨0, [t]⟩⟩
def np (t : Term) : Literal := ⟨false, ⟨0, [t]⟩⟩
def a : Term := .app 0 []

def problem : Problem := [
  [p (.var 0), p (.var 1), p (.var 0)],
  [np a]]

def certificate : Certificate := ⟨[
  .input 0,
  .input 1,
  .factor 0 0 1 [(1, .var 0)] [p (.var 0)],
  .resolve 2 0 1 0 [(0, a)] []], 3⟩

theorem dedup_example : preprocess problem = [[p (.var 0), p (.var 1)], [np a]] := by
  decide +kernel

theorem accepted : check (preprocess problem) certificate = true := by decide +kernel

theorem problem_unsat : ¬ Satisfiable problem :=
  check_preprocessed_sound problem certificate accepted

def functionProblem : Problem := [[p (.app 1 [.var 0])], [np (.app 1 [a])]]
def functionCertificate : Certificate := ⟨[
  .input 0, .input 1, .resolve 0 0 1 0 [(0, a)] []], 2⟩

theorem function_accepted : check functionProblem functionCertificate = true := by decide +kernel
theorem function_problem_unsat : ¬ Satisfiable functionProblem :=
  check_sound functionProblem functionCertificate function_accepted

theorem explicit_false_unsat : ¬ Satisfiable [[]] :=
  check_sound [[]] ⟨[.input 0], 0⟩ (by decide +kernel)

theorem same_position_factor_rejected :
    factor [p (.var 0)] 0 0 [] = none := by decide +kernel

theorem same_position_empty_forgery_rejected :
    check [[p (.var 0)]] ⟨[.input 0, .factor 0 0 0 [] []], 1⟩ = false := by decide +kernel

theorem ununified_resolution_rejected :
    resolve [p (.var 0)] 0 [np a] 0 [] = none := by decide +kernel

theorem same_polarity_resolution_rejected :
    resolve [p a] 0 [p a] 0 [] = none := by decide +kernel

theorem forward_parent_rejected :
    check [[p a], [np a]] ⟨[.input 0, .resolve 0 0 2 0 [] []], 1⟩ = false := by decide +kernel

theorem wrong_claim_rejected :
    check [[p a], [np a]]
      ⟨[.input 0, .input 1, .resolve 0 0 1 0 [] [p a]], 2⟩ = false := by decide +kernel

theorem duplicate_substitution_keys_rejected :
    resolve [p (.var 0)] 0 [np a] 0 [(0, a), (0, a)] = none := by decide +kernel

theorem wrong_final_rejected :
    check [[p a], [np a]]
      ⟨[.input 0, .input 1, .resolve 0 0 1 0 [] []], 0⟩ = false := by decide +kernel

/-- A simultaneous image is returned directly; it is not substituted twice. -/
theorem simultaneous_substitution :
    Term.subst [(0, .var 1), (1, a)] (.var 0) = .var 1 := by decide +kernel

end Fang.Examples

#print axioms Fang.Term.eval_subst
#print axioms Fang.preprocess_preserves_models
#print axioms Fang.factor_valid
#print axioms Fang.resolve_valid
#print axioms Fang.check_sound
#print axioms Fang.check_preprocessed_sound
#print axioms Fang.Examples.problem_unsat
#print axioms Fang.Examples.function_problem_unsat
