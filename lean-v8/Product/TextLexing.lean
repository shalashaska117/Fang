/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Product.NameSpelling

/-! The bytes of an exported clause: the lexemes of the source grammar, with
TPTP lower words and single-quoted atoms as names. A quoted atom reads as the
name it denotes, so `'abc'` and `abc` are one name and `'E'` is not `e`, as in
TPTP. The tokens are the source grammar's, so its clause grammar applies
unchanged. -/

namespace Fang.TstpText

open Source.Grammar

inductive TextWord (bytes : Bytes) : Token → Prop where
  | lower (name : String) (text : bytes = spelling name) (valid : LowerWord name) :
      TextWord bytes (.lower name)
  | variableWord (name : String) (text : bytes = spelling name) (valid : VariableName name) :
      TextWord bytes (.variable name)
  | falsity (text : bytes = spelling "$false") : TextWord bytes .falseLiteral

theorem lowerWord_not_variable {name : String} (lower : LowerWord name) (upper : VariableName name) :
    False := by
  obtain ⟨first, rest, bytes, firstLower, _⟩ := lower
  obtain ⟨other, others, otherBytes, firstUpper, _⟩ := upper
  have equal := (List.cons.inj (bytes.symm.trans otherBytes)).1
  subst other
  simp only [IsLower, IsUpper] at *
  omega

theorem false_not_lowerWord : ¬ LowerWord "$false" := by
  rintro ⟨first, rest, bytes, firstLower, _⟩
  change ([36, 102, 97, 108, 115, 101] : Bytes) = first :: rest at bytes
  have equal := (List.cons.inj bytes).1
  subst first
  simp [IsLower] at firstLower

theorem TextWord.unique {bytes left right} (first : TextWord bytes left) (second : TextWord bytes right) :
    left = right := by
  cases first with
  | lower name text valid =>
    cases second with
    | lower other otherText _ =>
      have equal := spelling_injective (text.symm.trans otherText)
      subst other
      rfl
    | variableWord other otherText otherValid =>
      have equal := spelling_injective (text.symm.trans otherText)
      subst other
      exact False.elim (lowerWord_not_variable valid otherValid)
    | falsity otherText =>
      have equal := spelling_injective (text.symm.trans otherText)
      subst name
      exact False.elim (false_not_lowerWord valid)
  | variableWord name text valid =>
    cases second with
    | lower other otherText otherValid =>
      have equal := spelling_injective (otherText.symm.trans text)
      subst other
      exact False.elim (lowerWord_not_variable otherValid valid)
    | variableWord other otherText _ =>
      have equal := spelling_injective (text.symm.trans otherText)
      subst other
      rfl
    | falsity otherText =>
      have equal := spelling_injective (text.symm.trans otherText)
      subst name
      exact False.elim (false_not_variable valid)
  | falsity text =>
    cases second with
    | lower other otherText otherValid =>
      have equal := spelling_injective (otherText.symm.trans text)
      subst other
      exact False.elim (false_not_lowerWord otherValid)
    | variableWord other otherText otherValid =>
      have equal := spelling_injective (otherText.symm.trans text)
      subst other
      exact False.elim (false_not_variable otherValid)
    | falsity => rfl

theorem TextWord.word_bytes {bytes token} (word : TextWord bytes token) :
    bytes ≠ [] ∧ ∀ byte ∈ bytes, IsWord byte := by
  cases word with
  | lower name text valid =>
    obtain ⟨first, rest, shape, firstLower, remaining⟩ := valid
    rw [text, shape]
    constructor
    · simp
    · intro byte member
      rcases List.mem_cons.mp member with equal | member
      · subst byte; exact Or.inl firstLower
      · have property := remaining byte member
        simp only [IsWord, IsLower, IsUpper, IsDigit] at *
        omega
  | variableWord name text valid =>
    obtain ⟨first, rest, shape, firstUpper, remaining⟩ := valid
    rw [text, shape]
    constructor
    · simp
    · intro byte member
      rcases List.mem_cons.mp member with equal | member
      · subst byte; exact Or.inr (Or.inl firstUpper)
      · have property := remaining byte member
        simp only [IsWord, IsLower, IsUpper, IsDigit] at *
        omega
  | falsity text =>
    rw [text]
    change ([36, 102, 97, 108, 115, 101] : Bytes) ≠ [] ∧
      ∀ byte ∈ ([36, 102, 97, 108, 115, 101] : Bytes), IsWord byte
    simp [IsWord, IsLower, IsUpper, IsDigit]

inductive TextLexeme : Bytes → Token → Bytes → Prop where
  | word {input front rest token}
      (shape : input = front ++ rest) (boundary : MaximalPrefix IsWord front rest)
      (spelled : TextWord front token) : TextLexeme input token rest
  | quoted {input text name rest}
      (shape : input = spelling text ++ rest) (atom : QuotedAtom text.toList name.toList) :
      TextLexeme input (.lower name) rest
  | punctuation {byte token rest} (spelled : Punctuation byte token) :
      TextLexeme (byte :: rest) token rest

theorem quote_not_word : ¬ IsWord 39 := by
  simp [IsWord, IsLower, IsUpper, IsDigit]

theorem quote_not_space : ¬ IsSpace 39 := by
  simp [IsSpace]

theorem quote_not_punctuation {token : Token} : ¬ Punctuation 39 token := by
  intro punctuation
  cases punctuation

theorem TextLexeme.nonempty {input token rest} (lexeme : TextLexeme input token rest) : input ≠ [] := by
  cases lexeme with
  | word shape boundary word =>
    rw [shape]
    intro empty
    exact word.word_bytes.1 (List.append_eq_nil_iff.mp empty).1
  | quoted shape atom =>
    obtain ⟨tail, spelled⟩ := quoted_spelling atom
    rw [shape, spelled]
    simp
  | punctuation => simp

theorem TextLexeme.head_not_space {byte tail token rest}
    (lexeme : TextLexeme (byte :: tail) token rest) : ¬ IsSpace byte := by
  cases lexeme with
  | word shape boundary word =>
    rename_i front
    cases front with
    | nil => exact False.elim (word.word_bytes.1 rfl)
    | cons head heads =>
      have equal := (List.cons.inj shape).1
      subst byte
      exact word_not_space (word.word_bytes.2 head List.mem_cons_self)
  | quoted shape atom =>
    obtain ⟨others, spelled⟩ := quoted_spelling atom
    rw [spelled] at shape
    have equal := (List.cons.inj shape).1
    subst byte
    exact quote_not_space
  | punctuation spelled => exact spelled.not_space

theorem text_word_cannot_start_punctuation {front rest byte tail token punct}
    (word : TextWord front token) (punctuation : Punctuation byte punct)
    (shape : front ++ rest = byte :: tail) : False := by
  cases front with
  | nil => exact word.word_bytes.1 rfl
  | cons head heads =>
    have equal := (List.cons.inj shape).1
    subst byte
    exact punctuation.not_word (word.word_bytes.2 head List.mem_cons_self)

theorem text_word_cannot_start_quote {front rest : Bytes} {text name : String} {tail : Bytes} {token : Token}
    (word : TextWord front token) (atom : QuotedAtom text.toList name.toList)
    (shape : front ++ rest = spelling text ++ tail) : False := by
  obtain ⟨others, spelled⟩ := quoted_spelling atom
  rw [spelled] at shape
  cases front with
  | nil => exact word.word_bytes.1 rfl
  | cons head heads =>
    have equal := (List.cons.inj shape).1
    subst head
    exact quote_not_word (word.word_bytes.2 39 List.mem_cons_self)

theorem quote_cannot_start_punctuation {text name : String} {rest : Bytes} {byte : UInt8} {tail : Bytes} {punct : Token}
    (atom : QuotedAtom text.toList name.toList) (punctuation : Punctuation byte punct)
    (shape : spelling text ++ rest = byte :: tail) : False := by
  obtain ⟨others, spelled⟩ := quoted_spelling atom
  rw [spelled] at shape
  have equal := (List.cons.inj shape).1
  subst byte
  exact quote_not_punctuation punctuation

theorem TextLexeme.unique {input left right leftRest rightRest}
    (first : TextLexeme input left leftRest) (second : TextLexeme input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | word shape boundary word =>
    cases second with
    | word otherShape otherBoundary otherWord =>
      obtain ⟨frontEqual, restEqual⟩ := boundary.unique otherBoundary (shape.symm.trans otherShape)
      subst frontEqual
      exact ⟨word.unique otherWord, restEqual⟩
    | quoted otherShape atom =>
      exact False.elim (text_word_cannot_start_quote word atom (shape.symm.trans otherShape))
    | punctuation punctuation =>
      exact False.elim (text_word_cannot_start_punctuation word punctuation shape.symm)
  | quoted shape atom =>
    cases second with
    | word otherShape otherBoundary otherWord =>
      exact False.elim (text_word_cannot_start_quote otherWord atom (otherShape.symm.trans shape))
    | quoted otherShape otherAtom =>
      obtain ⟨textEqual, restEqual⟩ := quoted_prefix_bytes atom otherAtom (shape.symm.trans otherShape)
      subst textEqual
      have names := QuotedAtom.functional atom otherAtom
      exact ⟨by rw [String.toList_inj.mp names], restEqual⟩
    | punctuation punctuation =>
      exact False.elim (quote_cannot_start_punctuation atom punctuation shape.symm)
  | punctuation punctuation =>
    cases second with
    | word shape boundary word =>
      exact False.elim (text_word_cannot_start_punctuation word punctuation shape.symm)
    | quoted shape atom =>
      exact False.elim (quote_cannot_start_punctuation atom punctuation shape.symm)
    | punctuation other => exact ⟨punctuation.unique other, rfl⟩

inductive TextTokenization : Bytes → List Token → Prop where
  | empty : TextTokenization [] []
  | whitespace {byte rest tokens} (space : IsSpace byte) (tail : TextTokenization rest tokens) :
      TextTokenization (byte :: rest) tokens
  | token {input head middle tail} (read : TextLexeme input head middle)
      (rest : TextTokenization middle tail) : TextTokenization input (head :: tail)

theorem TextTokenization.unique {input left right}
    (first : TextTokenization input left) (second : TextTokenization input right) : left = right := by
  induction first generalizing right with
  | empty =>
    cases second with
    | empty => rfl
    | token read _ => exact False.elim (read.nonempty rfl)
  | whitespace space tail induction =>
    cases second with
    | whitespace other otherTail => exact induction otherTail
    | token read _ => exact False.elim (read.head_not_space space)
  | token read rest induction =>
    cases second with
    | empty => exact False.elim (read.nonempty rfl)
    | whitespace space _ => exact False.elim (read.head_not_space space)
    | token other otherRest =>
      obtain ⟨tokenEqual, restEqual⟩ := read.unique other
      subst restEqual
      have tailsEqual := induction otherRest
      cases tokenEqual; cases tailsEqual
      rfl

theorem text_word_tokenization {bytes token} (word : TextWord bytes token) :
    TextTokenization bytes [token] := by
  apply TextTokenization.token (middle := [])
  · exact .word (by simp) ⟨word.word_bytes.2, by intros; contradiction⟩ word
  · exact .empty

/-- An atomic word is one name token. -/
theorem atomic_tokenization {text name : String} (word : AtomicText text name) :
    TextTokenization (spelling text) [.lower name] := by
  cases word with
  | lower valid =>
    exact text_word_tokenization (.lower text rfl valid)
  | quoted valid => exact .token (.quoted (rest := []) (by simp) valid) .empty

#print axioms Fang.TstpText.TextWord.unique
#print axioms Fang.TstpText.TextLexeme.unique
#print axioms Fang.TstpText.TextTokenization.unique
#print axioms Fang.TstpText.atomic_tokenization

end Fang.TstpText
