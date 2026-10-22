/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import TermRendering
import Init.Data.Nat.ToString

namespace Fang.TstpText

theorem variable_name_valid (index : Nat) : Frontend.variableName s!"X{index}" = true := by
  have digits : ∀ c ∈ Nat.toDigits 10 index, Frontend.asciiDigit c = true := by
    intro c present
    simpa [Char.isDigit, Frontend.asciiDigit, Char.le_def] using
      Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) present
  change Frontend.variableName ("X" ++ index.repr) = true
  simp only [Frontend.variableName, String.toList_append, Nat.toList_repr]
  change (Frontend.asciiUpper 'X' &&
    (Nat.toDigits 10 index).all (fun c =>
      Frontend.asciiLower c || Frontend.asciiUpper c || Frontend.asciiDigit c || c == '_')) = true
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · decide
  · intro c present
    simp [digits c present]

theorem variable_name_grammar (index : Nat) : Source.Grammar.VariableName s!"X{index}" :=
  (Frontend.variableName_iff _ (Frontend.variableName_ascii (variable_name_valid index))).mp
    (variable_name_valid index)

theorem variable_name_injective {left right : Nat}
    (equal : s!"X{left}" = s!"X{right}") : left = right := by
  have characters := congrArg String.toList equal
  simp only [String.toList_append, Nat.toString_eq_repr, Nat.toList_repr] at characters
  have digits : Nat.toDigits 10 left = Nat.toDigits 10 right := by simpa using characters
  have decoded := congrArg (fun chars => Nat.ofDigitChars 10 chars 0) digits
  simpa using decoded

end Fang.TstpText
