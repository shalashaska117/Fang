/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE.

Identifier classification by the actual frontend predicates. ASCII premises
are discharged for tokens returned by the proved lexer.
-/
import Fang.FrontendLexer

namespace Fang.Frontend

open Source.Grammar

theorem lowerTail_iff (character : Char) (ascii : character.toNat < 128) :
    (asciiLower character || asciiDigit character || character == '_') = true ↔
      IsLower (asciiByte character) ∨ IsDigit (asciiByte character) ∨
        (asciiByte character).toNat = 95 := by
  simp only [Bool.or_eq_true, asciiLower_iff character ascii, asciiDigit_iff character ascii,
    beq_iff_eq, char_eq_iff_nat, asciiByte_value character ascii]
  have underscore : '_'.toNat = 95 := rfl
  rw [underscore]
  exact or_assoc

theorem variableTail_iff (character : Char) (ascii : character.toNat < 128) :
    (asciiLower character || asciiUpper character || asciiDigit character || character == '_') = true ↔
      IsLower (asciiByte character) ∨ IsUpper (asciiByte character) ∨
        IsDigit (asciiByte character) ∨ (asciiByte character).toNat = 95 := by
  simp only [Bool.or_eq_true, asciiLower_iff character ascii, asciiUpper_iff character ascii,
    asciiDigit_iff character ascii, beq_iff_eq, char_eq_iff_nat,
    asciiByte_value character ascii]
  have underscore : '_'.toNat = 95 := rfl
  rw [underscore]
  simp only [or_assoc]

theorem lowerName_iff (name : String)
    (ascii : ∀ character ∈ name.toList, character.toNat < 128) :
    lowerName name = true ↔ LowerName name := by
  have encoded := spelling_ascii name ascii
  cases shape : name.toList with
  | nil =>
    simp [lowerName, shape, LowerName, encoded]
  | cons first rest =>
    have firstAscii : first.toNat < 128 := ascii first (by simp [shape])
    have restAscii : ∀ character ∈ rest, character.toNat < 128 := by
      intro character member
      exact ascii character (by simp [shape, member])
    simp only [shape, List.map_cons] at encoded
    simp only [lowerName, shape, Bool.and_eq_true, List.all_eq_true]
    constructor
    · rintro ⟨head, tail⟩
      refine ⟨asciiByte first, rest.map asciiByte, encoded,
        (asciiLower_iff first firstAscii).mp head, ?_⟩
      intro byte member
      obtain ⟨character, present, rfl⟩ := List.mem_map.mp member
      exact (lowerTail_iff character (restAscii character present)).mp (tail character present)
    · rintro ⟨byte, bytes, text, head, tail⟩
      have same := List.cons.inj (encoded.symm.trans text)
      obtain ⟨rfl, rfl⟩ := same
      refine ⟨(asciiLower_iff first firstAscii).mpr head, ?_⟩
      intro character member
      exact (lowerTail_iff character (restAscii character member)).mpr
        (tail (asciiByte character) (List.mem_map.mpr ⟨character, member, rfl⟩))

theorem variableName_iff (name : String)
    (ascii : ∀ character ∈ name.toList, character.toNat < 128) :
    variableName name = true ↔ VariableName name := by
  have encoded := spelling_ascii name ascii
  cases shape : name.toList with
  | nil =>
    simp [variableName, shape, VariableName, encoded]
  | cons first rest =>
    have firstAscii : first.toNat < 128 := ascii first (by simp [shape])
    have restAscii : ∀ character ∈ rest, character.toNat < 128 := by
      intro character member
      exact ascii character (by simp [shape, member])
    simp only [shape, List.map_cons] at encoded
    simp only [variableName, shape, Bool.and_eq_true, List.all_eq_true]
    constructor
    · rintro ⟨head, tail⟩
      refine ⟨asciiByte first, rest.map asciiByte, encoded,
        (asciiUpper_iff first firstAscii).mp head, ?_⟩
      intro byte member
      obtain ⟨character, present, rfl⟩ := List.mem_map.mp member
      exact (variableTail_iff character (restAscii character present)).mp (tail character present)
    · rintro ⟨byte, bytes, text, head, tail⟩
      have same := List.cons.inj (encoded.symm.trans text)
      obtain ⟨rfl, rfl⟩ := same
      refine ⟨(asciiUpper_iff first firstAscii).mpr head, ?_⟩
      intro character member
      exact (variableTail_iff character (restAscii character member)).mpr
        (tail (asciiByte character) (List.mem_map.mpr ⟨character, member, rfl⟩))

theorem RawTokenization.token_ascii {input : List Char} {offset : Nat} {tokens : List Token}
    (parsed : RawTokenization input offset tokens) :
    ∀ token ∈ tokens, ∀ character ∈ token.text.toList, character.toNat < 128 := by
  induction parsed with
  | empty => simp
  | whitespace space tail ih => exact ih
  | @word front rest offset tokens nonempty maximal tail ih =>
    intro token member character present
    rcases List.mem_cons.mp member with rfl | member
    · have member : character ∈ front := by simpa using present
      exact (maximal.members character member).1
    · exact ih token member character present
  | @punctuation first rest offset tokens punctuation tail ih =>
    intro token member character present
    rcases List.mem_cons.mp member with rfl | member
    · have same : character = first := by simpa using present
      subst character
      exact rawPunctuation_ascii punctuation
    · exact ih token member character present

theorem tokenize_token_ascii (input : String) (tokens : List Token)
    (success : tokenize input = .ok tokens) :
    ∀ token ∈ tokens, ∀ character ∈ token.text.toList, character.toNat < 128 :=
  (tokenize_sound input tokens success).token_ascii

theorem rawTokenSpelling_lower (raw : Token)
    (ascii : ∀ character ∈ raw.text.toList, character.toNat < 128)
    (valid : lowerName raw.text = true) : RawTokenSpelling raw (.lower raw.text) :=
  Or.inl (.lower raw.text rfl ((lowerName_iff raw.text ascii).mp valid))

theorem rawTokenSpelling_variable (raw : Token)
    (ascii : ∀ character ∈ raw.text.toList, character.toNat < 128)
    (valid : variableName raw.text = true) : RawTokenSpelling raw (.variable raw.text) :=
  Or.inl (.variableWord raw.text rfl ((variableName_iff raw.text ascii).mp valid))

theorem rawTokenSpelling_false (raw : Token) (text : raw.text = "$false") :
    RawTokenSpelling raw .falseLiteral := by
  exact Or.inl (.falsity (congrArg spelling text))

theorem rawTokenSpelling_punctuation (raw : Token) (character : Char)
    (punctuation : RawPunctuation character) (text : raw.text = String.singleton character)
    (token : Source.Grammar.Token) (spelled : Punctuation (asciiByte character) token) :
    RawTokenSpelling raw token := by
  refine Or.inr ⟨asciiByte character, spelled, ?_⟩
  rw [text]
  exact spelling_ofList_ascii [character] (by
    intro item member
    have same : item = character := by simpa using member
    subst item
    exact rawPunctuation_ascii punctuation)

theorem RawTokenSpelling.unique {raw : Token} {left right : Source.Grammar.Token}
    (first : RawTokenSpelling raw left) (second : RawTokenSpelling raw right) : left = right := by
  rcases first with word | ⟨byte, punctuation, text⟩
  · rcases second with other | ⟨byte, punctuation, text⟩
    · exact word.unique other
    · rw [text] at word
      exact False.elim (punctuation.not_word (word.word_bytes.2 byte List.mem_cons_self))
  · rcases second with word | ⟨other, otherPunctuation, otherText⟩
    · rw [text] at word
      exact False.elim (punctuation.not_word (word.word_bytes.2 byte List.mem_cons_self))
    · have same := (List.cons.inj (text.symm.trans otherText)).1
      subst other
      exact punctuation.unique otherPunctuation

theorem ClassifiedTokens.unique {raw : List Token} {left right : List Source.Grammar.Token}
    (first : ClassifiedTokens raw left) (second : ClassifiedTokens raw right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
    cases second with
    | cons other otherTail =>
      rw [head.unique other, ih otherTail]

theorem ClassifiedTokens.append {leftRaw rightRaw : List Token}
    {left right : List Source.Grammar.Token}
    (first : ClassifiedTokens leftRaw left) (second : ClassifiedTokens rightRaw right) :
    ClassifiedTokens (leftRaw ++ rightRaw) (left ++ right) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

theorem variableName_not_lowerName (name : String)
    (ascii : ∀ character ∈ name.toList, character.toNat < 128)
    (isVariable : variableName name = true) : lowerName name = false := by
  cases lower : lowerName name with
  | false => rfl
  | true =>
    exact False.elim (name_kinds_disjoint ((lowerName_iff name ascii).mp lower)
      ((variableName_iff name ascii).mp isVariable))

theorem punctuation_byte_values {byte : UInt8} {token : Source.Grammar.Token}
    (spelled : Punctuation byte token) :
    byte.toNat = 40 ∨ byte.toNat = 41 ∨ byte.toNat = 44 ∨
      byte.toNat = 46 ∨ byte.toNat = 124 ∨ byte.toNat = 126 := by
  cases spelled <;> simp

theorem rawPunctuation_of_spelled (character : Char) (ascii : character.toNat < 128)
    (token : Source.Grammar.Token) (spelled : Punctuation (asciiByte character) token) :
    RawPunctuation character := by
  have values := punctuation_byte_values spelled
  rw [asciiByte_value character ascii] at values
  simp only [RawPunctuation, char_eq_iff_nat]
  exact values

theorem rawTokenization_of_grammar {bytes : Bytes} {tokens : List Source.Grammar.Token}
    (parsed : Source.Grammar.Tokenization bytes tokens)
    (characters : List Char) (offset : Nat)
    (encoded : characters.map asciiByte = bytes)
    (ascii : ∀ character ∈ characters, character.toNat < 128) :
    ∃ raw, RawTokenization characters offset raw ∧ ClassifiedTokens raw tokens := by
  induction parsed generalizing characters offset with
  | empty =>
    have empty : characters = [] := List.map_eq_nil_iff.mp encoded
    subst characters
    exact ⟨[], .empty offset, .nil⟩
  | @whitespace byte rest tokens space tail ih =>
    cases characters with
    | nil => cases encoded
    | cons character characters =>
      have equal := List.cons.inj encoded
      obtain ⟨rfl, tailBytes⟩ := equal
      have remaining : ∀ item ∈ characters, item.toNat < 128 := by
        intro item member
        exact ascii item (List.mem_cons_of_mem _ member)
      obtain ⟨raw, scanned, classified⟩ := ih characters (offset + 1) tailBytes remaining
      exact ⟨raw, .whitespace ⟨ascii character List.mem_cons_self, space⟩ scanned, classified⟩
  | @token input head middle tokens lexeme tail ih =>
    cases lexeme with
    | word shape maximal spelled =>
      rename_i front
      have mappedShape := encoded.trans shape
      have frontBytes : (characters.take front.length).map asciiByte = front := by
        rw [List.map_take, mappedShape]
        simp
      have restBytes : (characters.drop front.length).map asciiByte = middle := by
        rw [List.map_drop, mappedShape]
        simp
      have frontAscii : ∀ character ∈ characters.take front.length, character.toNat < 128 := by
        intro character member
        exact ascii character (List.mem_of_mem_take member)
      have restAscii : ∀ character ∈ characters.drop front.length, character.toNat < 128 := by
        intro character member
        exact ascii character (List.mem_of_mem_drop member)
      have frontNonempty : characters.take front.length ≠ [] := by
        intro empty
        rw [empty] at frontBytes
        exact spelled.word_bytes.1 frontBytes.symm
      have rawMaximal : MaximalPrefix RawWord
          (characters.take front.length) (characters.drop front.length) := by
        constructor
        · intro character member
          refine ⟨frontAscii character member, ?_⟩
          apply maximal.members (asciiByte character)
          rw [← frontBytes]
          exact List.mem_map.mpr ⟨character, member, rfl⟩
        · intro character remaining shape word
          have byteShape : middle = asciiByte character :: remaining.map asciiByte := by
            rw [← restBytes, shape]
            rfl
          exact maximal.boundary _ _ byteShape word.2
      obtain ⟨raw, scanned, classified⟩ := ih (characters.drop front.length)
        (offset + (characters.take front.length).length) restBytes restAscii
      have rawPrefix := RawTokenization.word frontNonempty rawMaximal scanned
      refine ⟨{ text := String.ofList (characters.take front.length), offset } :: raw, ?_, ?_⟩
      · simpa only [List.take_append_drop] using rawPrefix
      · apply ClassifiedTokens.cons _ classified
        apply Or.inl
        have spellingEqual := (spelling_ofList_ascii (characters.take front.length) frontAscii).trans frontBytes
        simpa only [spellingEqual] using spelled
    | punctuation spelled =>
      cases characters with
      | nil => cases encoded
      | cons character characters =>
        obtain ⟨rfl, tailBytes⟩ := List.cons.inj encoded
        have firstAscii := ascii character List.mem_cons_self
        have remaining : ∀ item ∈ characters, item.toNat < 128 := by
          intro item member
          exact ascii item (List.mem_cons_of_mem _ member)
        obtain ⟨raw, scanned, classified⟩ := ih characters (offset + 1) tailBytes remaining
        have punctuation := rawPunctuation_of_spelled character firstAscii head spelled
        refine ⟨{ text := String.singleton character, offset } :: raw,
          .punctuation punctuation scanned, .cons ?_ classified⟩
        exact rawTokenSpelling_punctuation _ character punctuation rfl head spelled

theorem grammar_tokenization_complete (input : String) (tokens : List Source.Grammar.Token)
    (ascii : ∀ character ∈ input.toList, character.toNat < 128)
    (parsed : Source.Grammar.Tokenization (spelling input) tokens) :
    ∃ raw, tokenize input = .ok raw ∧ ClassifiedTokens raw tokens := by
  obtain ⟨raw, scanned, classified⟩ := rawTokenization_of_grammar parsed input.toList 0
    (spelling_ascii input ascii).symm ascii
  exact ⟨raw, tokenize_complete input raw scanned, classified⟩

theorem grammar_tokenization_iff (input : String) (tokens : List Source.Grammar.Token)
    (ascii : ∀ character ∈ input.toList, character.toNat < 128) :
    Source.Grammar.Tokenization (spelling input) tokens ↔
      ∃ raw, tokenize input = .ok raw ∧ ClassifiedTokens raw tokens := by
  constructor
  · exact grammar_tokenization_complete input tokens ascii
  · rintro ⟨raw, success, classified⟩
    exact tokenize_toGrammar input raw success tokens classified

end Fang.Frontend

#print axioms Fang.Frontend.lowerName_iff
#print axioms Fang.Frontend.variableName_iff
#print axioms Fang.Frontend.tokenize_token_ascii
#print axioms Fang.Frontend.RawTokenSpelling.unique
#print axioms Fang.Frontend.ClassifiedTokens.unique
#print axioms Fang.Frontend.grammar_tokenization_iff
