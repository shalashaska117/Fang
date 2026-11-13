/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
ASCII consequences of the independent byte grammar, including the reverse
UTF-8 bridge. No executable parser acceptance is assumed here.
-/
import Fang.SourceAscii

namespace Fang.Source.Grammar

theorem IsWord.ascii {byte : UInt8} (word : IsWord byte) : byte.toNat < 128 := by
  simp only [IsWord, IsLower, IsUpper, IsDigit] at word
  omega

theorem IsSpace.ascii {byte : UInt8} (space : IsSpace byte) : byte.toNat < 128 := by
  simp only [IsSpace] at space
  omega

theorem Punctuation.ascii {byte : UInt8} {token : Token}
    (punctuation : Punctuation byte token) : byte.toNat < 128 := by
  cases punctuation <;> decide

theorem WordSpelling.ascii {bytes : Bytes} {token : Token}
    (spelled : WordSpelling bytes token) : ∀ byte ∈ bytes, byte.toNat < 128 := by
  intro byte member
  exact (spelled.word_bytes.2 byte member).ascii

theorem Lexeme.ascii {input rest : Bytes} {token : Token}
    (lexeme : Lexeme input token rest)
    (remaining : ∀ byte ∈ rest, byte.toNat < 128) :
    ∀ byte ∈ input, byte.toNat < 128 := by
  cases lexeme with
  | word shape maximal spelled =>
      rw [shape]
      intro byte member
      rcases List.mem_append.mp member with front | tail
      · exact spelled.ascii byte front
      · exact remaining byte tail
  | punctuation spelled =>
      intro byte member
      rcases List.mem_cons.mp member with rfl | tail
      · exact spelled.ascii
      · exact remaining byte tail

theorem Tokenization.ascii {bytes : Bytes} {tokens : List Token}
    (tokenized : Tokenization bytes tokens) : ∀ byte ∈ bytes, byte.toNat < 128 := by
  induction tokenized with
  | empty => simp
  | whitespace space tail induction =>
      intro byte member
      rcases List.mem_cons.mp member with rfl | remaining
      · exact space.ascii
      · exact induction byte remaining
  | token lexeme tail induction => exact lexeme.ascii induction

theorem Parses.ascii {bytes : Bytes} {problem : Problem} (parsed : Parses bytes problem) :
    ∀ byte ∈ bytes, byte.toNat < 128 := by
  obtain ⟨tokens, tokenized, _⟩ := parsed
  exact tokenized.ascii

def byteChar (byte : UInt8) : Char := Char.ofNat byte.toNat

theorem byteChar_value (byte : UInt8) (ascii : byte.toNat < 128) :
    (byteChar byte).toNat = byte.toNat := by
  have valid : byte.toNat.isValidChar := Or.inl (by omega)
  simp only [byteChar, Char.ofNat, dite_eq_left valid]
  rfl

theorem byteChar_ascii (byte : UInt8) (ascii : byte.toNat < 128) :
    (byteChar byte).toNat < 128 := by
  rw [byteChar_value byte ascii]
  exact ascii

theorem asciiByte_byteChar (byte : UInt8) (ascii : byte.toNat < 128) :
    asciiByte (byteChar byte) = byte := by
  apply UInt8.toNat_inj.mp
  rw [asciiByte_value _ (byteChar_ascii byte ascii), byteChar_value byte ascii]

theorem ascii_string_of_bytes (bytes : Bytes)
    (ascii : ∀ byte ∈ bytes, byte.toNat < 128) :
    spelling (String.ofList (bytes.map byteChar)) = bytes := by
  rw [spelling_ofList_ascii]
  · simp only [List.map_map]
    induction bytes with
    | nil => rfl
    | cons byte rest induction =>
        simp only [List.map_cons, Function.comp_apply]
        rw [asciiByte_byteChar byte (ascii byte List.mem_cons_self)]
        exact congrArg (List.cons byte)
          (induction (fun other member => ascii other (List.mem_cons_of_mem byte member)))
  · intro character member
    obtain ⟨byte, byteMember, rfl⟩ := List.mem_map.mp member
    exact byteChar_ascii byte (ascii byte byteMember)

theorem string_ascii_of_spelling (input : String)
    (ascii : ∀ byte ∈ spelling input, byte.toNat < 128) :
    ∀ character ∈ input.toList, character.toNat < 128 := by
  have reconstructed : String.ofList ((spelling input).map byteChar) = input :=
    spelling_injective (ascii_string_of_bytes (spelling input) ascii)
  intro character member
  rw [← reconstructed] at member
  simp only [String.toList_ofList, List.mem_map] at member
  obtain ⟨byte, byteMember, rfl⟩ := member
  exact byteChar_ascii byte (ascii byte byteMember)

theorem spelling_ascii_iff (input : String) :
    (∀ byte ∈ spelling input, byte.toNat < 128) ↔
      ∀ character ∈ input.toList, character.toNat < 128 := by
  constructor
  · exact string_ascii_of_spelling input
  · intro ascii byte member
    rw [spelling_ascii input ascii] at member
    obtain ⟨character, charMember, rfl⟩ := List.mem_map.mp member
    rw [asciiByte_value character (ascii character charMember)]
    exact ascii character charMember

theorem Tokenization.string_ascii {input : String} {tokens : List Token}
    (tokenized : Tokenization (spelling input) tokens) :
    ∀ character ∈ input.toList, character.toNat < 128 :=
  string_ascii_of_spelling input tokenized.ascii

theorem Parses.string_ascii {input : String} {problem : Problem}
    (parsed : Parses (spelling input) problem) :
    ∀ character ∈ input.toList, character.toNat < 128 :=
  string_ascii_of_spelling input parsed.ascii

#print axioms Tokenization.ascii
#print axioms Parses.ascii
#print axioms ascii_string_of_bytes
#print axioms spelling_ascii_iff
#print axioms Tokenization.string_ascii
#print axioms Parses.string_ascii

end Fang.Source.Grammar
