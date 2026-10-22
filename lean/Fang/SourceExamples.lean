/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

An explicit named-syntax witness for the documented factoring example.
No theorem here associates this syntax with input bytes.
-/
import Fang.SourceSemantics
import Fang.Examples

namespace Fang.Source.Examples

def signature : Signature :=
  ⟨fun name => if name == "a" then some 0 else none,
   fun name => if name == "p" then some 1 else none⟩

def symbols : Symbols := ⟨fun _ => 0, fun _ => "a", fun _ => 0, fun _ => "p"⟩

def variables : Variables :=
  ⟨fun name => if name == "Y" then 1 else 0,
   fun id => if id == 1 then "Y" else "X"⟩

def positive (term : Term) : Literal := ⟨true, "p", [term]⟩
def negative (term : Term) : Literal := ⟨false, "p", [term]⟩

def problem : Problem := [
  ⟨"c0", [positive (.var "X"), positive (.var "Y"), positive (.var "X")]⟩,
  ⟨"c1", [negative (.app "a" [])]⟩]

theorem x_encoded : TermEncoding signature symbols variables (.var "X") (.var 0) :=
  .var "X" (by decide)

theorem y_encoded : TermEncoding signature symbols variables (.var "Y") (.var 1) :=
  .var "Y" (by decide)

theorem a_encoded : TermEncoding signature symbols variables (.app "a" []) (.app 0 []) :=
  .app "a" [] [] (by decide) (by decide) .nil

theorem positive_encoded {named numeric}
    (term : TermEncoding signature symbols variables named numeric) :
    LiteralEncoding signature symbols variables (positive named) (Fang.Examples.p numeric) :=
  ⟨rfl, rfl, rfl, rfl, .cons term .nil⟩

theorem negative_encoded {named numeric}
    (term : TermEncoding signature symbols variables named numeric) :
    LiteralEncoding signature symbols variables (negative named) (Fang.Examples.np numeric) :=
  ⟨rfl, rfl, rfl, rfl, .cons term .nil⟩

theorem encoded : ProblemEncoding signature symbols problem Fang.Examples.problem := by
  refine ⟨by decide, .cons ?_ (.cons ?_ .nil)⟩
  · exact ⟨variables, .cons (positive_encoded x_encoded)
      (.cons (positive_encoded y_encoded) (.cons (positive_encoded x_encoded) .nil))⟩
  · exact ⟨variables, .cons (negative_encoded a_encoded) .nil⟩

theorem named_problem_unsat : ¬ Satisfiable problem :=
  encoded.unsat_of_check Fang.Examples.certificate Fang.Examples.accepted

#print axioms encoded
#print axioms named_problem_unsat

end Fang.Source.Examples
