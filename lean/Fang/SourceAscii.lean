/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Correspondence between executable character predicates and independent byte classes.
This does not yet prove tokenization or parsing correctness.
-/
import Fang.Input
import Fang.SourceLexing
import Init.Data.Char.Lemmas

namespace Fang.Source.Grammar

def asciiByte (character : Char) : UInt8 := UInt8.ofNat character.toNat

theorem asciiByte_value (character : Char) (ascii : character.toNat < 128) :
    (asciiByte character).toNat = character.toNat := by
  simp only [asciiByte, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem asciiLower_nat (character : Char) :
    Frontend.asciiLower character = true ↔ 97 ≤ character.toNat ∧ character.toNat ≤ 122 := by
  simp [Frontend.asciiLower, Char.le_def, UInt32.le_iff_toNat_le]

theorem asciiUpper_nat (character : Char) :
    Frontend.asciiUpper character = true ↔ 65 ≤ character.toNat ∧ character.toNat ≤ 90 := by
  simp [Frontend.asciiUpper, Char.le_def, UInt32.le_iff_toNat_le]

theorem asciiDigit_nat (character : Char) :
    Frontend.asciiDigit character = true ↔ 48 ≤ character.toNat ∧ character.toNat ≤ 57 := by
  simp [Frontend.asciiDigit, Char.le_def, UInt32.le_iff_toNat_le]

theorem asciiLower_iff (character : Char) (ascii : character.toNat < 128) :
    Frontend.asciiLower character = true ↔ IsLower (asciiByte character) := by
  rw [asciiLower_nat]
  simp [IsLower, asciiByte_value character ascii]

theorem asciiUpper_iff (character : Char) (ascii : character.toNat < 128) :
    Frontend.asciiUpper character = true ↔ IsUpper (asciiByte character) := by
  rw [asciiUpper_nat]
  simp [IsUpper, asciiByte_value character ascii]

theorem asciiDigit_iff (character : Char) (ascii : character.toNat < 128) :
    Frontend.asciiDigit character = true ↔ IsDigit (asciiByte character) := by
  rw [asciiDigit_nat]
  simp [IsDigit, asciiByte_value character ascii]

theorem char_eq_iff_nat (left right : Char) : left = right ↔ left.toNat = right.toNat := by
  constructor
  · intro same; rw [same]
  · intro same
    exact Char.ext (UInt32.toNat_inj.mp same)

theorem asciiSpace_iff (character : Char) (ascii : character.toNat < 128) :
    Frontend.asciiSpace character = true ↔ IsSpace (asciiByte character) := by
  simp [Frontend.asciiSpace, IsSpace, asciiByte_value character ascii,
    char_eq_iff_nat]

theorem wordChar_iff (character : Char) (ascii : character.toNat < 128) :
    Frontend.wordChar character = true ↔ IsWord (asciiByte character) := by
  simp [Frontend.wordChar, IsWord, asciiLower_iff character ascii,
    asciiUpper_iff character ascii, asciiDigit_iff character ascii,
    asciiByte_value character ascii, char_eq_iff_nat, or_assoc]

theorem utf8EncodeChar_ascii (character : Char) (ascii : character.toNat < 128) :
    String.utf8EncodeChar character = [asciiByte character] := by
  have bounded : character.val.toNat ≤ 127 := by exact Nat.le_of_lt_succ ascii
  simp only [String.utf8EncodeChar, bounded, ite_true, asciiByte, Char.toNat]

theorem spelling_ofList_ascii (characters : List Char)
    (ascii : ∀ character ∈ characters, character.toNat < 128) :
    spelling (String.ofList characters) = characters.map asciiByte := by
  have encoded : characters.flatMap String.utf8EncodeChar = characters.map asciiByte := by
    induction characters with
    | nil => rfl
    | cons character rest ih =>
      have first := utf8EncodeChar_ascii character (ascii character List.mem_cons_self)
      have remaining := ih (fun item member => ascii item (List.mem_cons_of_mem _ member))
      simp [first, remaining]
  simpa [spelling, String.toByteArray_ofList, List.utf8Encode] using encoded

theorem spelling_ascii (input : String)
    (ascii : ∀ character ∈ input.toList, character.toNat < 128) :
    spelling input = input.toList.map asciiByte := by
  simpa using spelling_ofList_ascii input.toList ascii

end Fang.Source.Grammar

#print axioms Fang.Source.Grammar.asciiLower_iff
#print axioms Fang.Source.Grammar.asciiUpper_iff
#print axioms Fang.Source.Grammar.asciiDigit_iff
#print axioms Fang.Source.Grammar.asciiSpace_iff
#print axioms Fang.Source.Grammar.wordChar_iff
#print axioms Fang.Source.Grammar.spelling_ofList_ascii
#print axioms Fang.Source.Grammar.spelling_ascii
