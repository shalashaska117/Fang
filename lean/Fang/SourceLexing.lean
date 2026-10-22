/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

Independent ASCII byte classes and maximal-prefix relations for source lexing.
-/
import Fang.SourceGrammar

namespace Fang.Source.Grammar

abbrev Bytes := List UInt8

def spelling (name : String) : Bytes := name.toByteArray.data.toList

def IsSpace (byte : UInt8) : Prop :=
  byte.toNat = 32 ∨ (9 ≤ byte.toNat ∧ byte.toNat ≤ 13)

def IsLower (byte : UInt8) : Prop := 97 ≤ byte.toNat ∧ byte.toNat ≤ 122
def IsUpper (byte : UInt8) : Prop := 65 ≤ byte.toNat ∧ byte.toNat ≤ 90
def IsDigit (byte : UInt8) : Prop := 48 ≤ byte.toNat ∧ byte.toNat ≤ 57

def IsWord (byte : UInt8) : Prop :=
  IsLower byte ∨ IsUpper byte ∨ IsDigit byte ∨
    byte.toNat = 95 ∨ byte.toNat = 36 ∨ byte.toNat = 45

def LowerName (name : String) : Prop :=
  ∃ first rest, spelling name = first :: rest ∧ IsLower first ∧
    ∀ byte ∈ rest, IsLower byte ∨ IsDigit byte ∨ byte.toNat = 95

def VariableName (name : String) : Prop :=
  ∃ first rest, spelling name = first :: rest ∧ IsUpper first ∧
    ∀ byte ∈ rest, IsLower byte ∨ IsUpper byte ∨ IsDigit byte ∨ byte.toNat = 95

theorem word_not_space {byte : UInt8} (word : IsWord byte) : ¬ IsSpace byte := by
  simp only [IsWord, IsLower, IsUpper, IsDigit, IsSpace] at *
  omega

theorem spelling_injective {left right : String} (same : spelling left = spelling right) :
    left = right := by
  apply String.toByteArray_inj.mp
  have arrays := congrArg List.toArray same
  simp only [spelling, Array.toArray_toList] at arrays
  exact congrArg ByteArray.mk arrays

/- A maximal prefix states a boundary condition; it does not run a scanner. -/
structure MaximalPrefix (property : α → Prop) (front rest : List α) : Prop where
  members : ∀ item ∈ front, property item
  boundary : ∀ item tail, rest = item :: tail → ¬ property item

theorem MaximalPrefix.unique {property : α → Prop} {left right leftRest rightRest}
    (first : MaximalPrefix property left leftRest)
    (second : MaximalPrefix property right rightRest)
    (same : left ++ leftRest = right ++ rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact ⟨rfl, same⟩
      | cons head tail =>
          exact False.elim (first.boundary head (tail ++ rightRest) same
            (second.members head List.mem_cons_self))
  | cons head tail induction =>
      cases right with
      | nil =>
          exact False.elim (second.boundary head (tail ++ leftRest) same.symm
            (first.members head List.mem_cons_self))
      | cons other others =>
          have equal := List.cons.inj same
          cases equal.1
          have tailFirst : MaximalPrefix property tail leftRest :=
            ⟨fun item member => first.members item (List.mem_cons_of_mem _ member), first.boundary⟩
          have tailSecond : MaximalPrefix property others rightRest :=
            ⟨fun item member => second.members item (List.mem_cons_of_mem _ member), second.boundary⟩
          obtain ⟨prefixEqual, restEqual⟩ := induction tailFirst tailSecond equal.2
          exact ⟨congrArg (List.cons head) prefixEqual, restEqual⟩

theorem name_kinds_disjoint {name} (lower : LowerName name) (upper : VariableName name) : False := by
  obtain ⟨first, rest, bytes, firstLower, _⟩ := lower
  obtain ⟨other, others, otherBytes, firstUpper, _⟩ := upper
  have equal := (List.cons.inj (bytes.symm.trans otherBytes)).1
  subst other
  simp only [IsLower, IsUpper] at *
  omega

theorem false_not_lower : ¬ LowerName "$false" := by
  rintro ⟨first, rest, bytes, firstLower, _⟩
  change ([36, 102, 97, 108, 115, 101] : Bytes) = first :: rest at bytes
  have equal := (List.cons.inj bytes).1
  subst first
  simp [IsLower] at firstLower

theorem false_not_variable : ¬ VariableName "$false" := by
  rintro ⟨first, rest, bytes, firstUpper, _⟩
  change ([36, 102, 97, 108, 115, 101] : Bytes) = first :: rest at bytes
  have equal := (List.cons.inj bytes).1
  subst first
  simp [IsUpper] at firstUpper

inductive WordSpelling (bytes : Bytes) : Token → Prop where
  | lower (name : String) (text : bytes = spelling name) (valid : LowerName name) :
      WordSpelling bytes (.lower name)
  | variableWord (name : String) (text : bytes = spelling name) (valid : VariableName name) :
      WordSpelling bytes (.variable name)
  | falsity (text : bytes = spelling "$false") : WordSpelling bytes .falseLiteral

theorem WordSpelling.unique {bytes left right}
    (first : WordSpelling bytes left) (second : WordSpelling bytes right) : left = right := by
  cases first with
  | lower name text valid =>
      cases second with
      | lower other otherText otherValid =>
          exact congrArg Token.lower (spelling_injective (text.symm.trans otherText))
      | variableWord other otherText otherValid =>
          have equal := spelling_injective (text.symm.trans otherText)
          subst other
          exact False.elim (name_kinds_disjoint valid otherValid)
      | falsity otherText =>
          have equal := spelling_injective (text.symm.trans otherText)
          subst name
          exact False.elim (false_not_lower valid)
  | variableWord name text valid =>
      cases second with
      | lower other otherText otherValid =>
          have equal := spelling_injective (text.symm.trans otherText)
          subst other
          exact False.elim (name_kinds_disjoint otherValid valid)
      | variableWord other otherText otherValid =>
          exact congrArg Token.variable (spelling_injective (text.symm.trans otherText))
      | falsity otherText =>
          have equal := spelling_injective (text.symm.trans otherText)
          subst name
          exact False.elim (false_not_variable valid)
  | falsity text =>
      cases second with
      | lower other otherText otherValid =>
          have equal := spelling_injective (otherText.symm.trans text)
          subst other
          exact False.elim (false_not_lower otherValid)
      | variableWord other otherText otherValid =>
          have equal := spelling_injective (otherText.symm.trans text)
          subst other
          exact False.elim (false_not_variable otherValid)
      | falsity => rfl

theorem WordSpelling.word_bytes {bytes token} (word : WordSpelling bytes token) :
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

inductive Punctuation : UInt8 → Token → Prop where
  | lparen : Punctuation 40 .lparen
  | rparen : Punctuation 41 .rparen
  | comma : Punctuation 44 .comma
  | period : Punctuation 46 .period
  | disjoin : Punctuation 124 .disjoin
  | negate : Punctuation 126 .negate

theorem Punctuation.not_word {byte token} (punctuation : Punctuation byte token) :
    ¬ IsWord byte := by
  cases punctuation <;> simp [IsWord, IsLower, IsUpper, IsDigit]

theorem Punctuation.not_space {byte token} (punctuation : Punctuation byte token) :
    ¬ IsSpace byte := by
  cases punctuation <;> simp [IsSpace]

theorem Punctuation.unique {byte left right}
    (first : Punctuation byte left) (second : Punctuation byte right) : left = right := by
  cases first <;> cases second <;> rfl

inductive Lexeme : Bytes → Token → Bytes → Prop where
  | word {input front rest token}
      (shape : input = front ++ rest) (boundary : MaximalPrefix IsWord front rest)
      (spelled : WordSpelling front token) : Lexeme input token rest
  | punctuation {byte token rest} (spelled : Punctuation byte token) :
      Lexeme (byte :: rest) token rest

theorem Lexeme.nonempty {input token rest} (lexeme : Lexeme input token rest) : input ≠ [] := by
  cases lexeme with
  | word shape boundary word =>
      rw [shape]
      intro empty
      exact word.word_bytes.1 (List.append_eq_nil_iff.mp empty).1
  | punctuation => simp

theorem Lexeme.head_not_space {byte tail token rest}
    (lexeme : Lexeme (byte :: tail) token rest) : ¬ IsSpace byte := by
  cases lexeme with
  | word shape boundary word =>
      rename_i front
      cases front with
      | nil => exact False.elim (word.word_bytes.1 rfl)
      | cons head heads =>
          have equal := (List.cons.inj shape).1
          subst byte
          exact word_not_space (word.word_bytes.2 head List.mem_cons_self)
  | punctuation spelled => exact spelled.not_space

theorem word_cannot_start_punctuation {front rest byte tail token punct}
    (word : WordSpelling front token) (punctuation : Punctuation byte punct)
    (shape : front ++ rest = byte :: tail) : False := by
  cases front with
  | nil => exact word.word_bytes.1 rfl
  | cons head heads =>
      have equal := (List.cons.inj shape).1
      subst byte
      exact punctuation.not_word (word.word_bytes.2 head List.mem_cons_self)

theorem Lexeme.unique {input left right leftRest rightRest}
    (first : Lexeme input left leftRest) (second : Lexeme input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | word shape boundary word =>
      cases second with
      | word otherShape otherBoundary otherWord =>
          obtain ⟨frontEqual, restEqual⟩ := boundary.unique otherBoundary (shape.symm.trans otherShape)
          subst frontEqual
          exact ⟨word.unique otherWord, restEqual⟩
      | punctuation punctuation =>
          exact False.elim (word_cannot_start_punctuation word punctuation shape.symm)
  | punctuation punctuation =>
      cases second with
      | word shape boundary word =>
          exact False.elim (word_cannot_start_punctuation word punctuation shape.symm)
      | punctuation other => exact ⟨punctuation.unique other, rfl⟩

inductive Tokenization : Bytes → List Token → Prop where
  | empty : Tokenization [] []
  | whitespace {byte rest tokens} (space : IsSpace byte) (tail : Tokenization rest tokens) :
      Tokenization (byte :: rest) tokens
  | token {input head middle tail} (read : Lexeme input head middle)
      (rest : Tokenization middle tail) : Tokenization input (head :: tail)

theorem Tokenization.unique {input left right}
    (first : Tokenization input left) (second : Tokenization input right) : left = right := by
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

def Parses (bytes : Bytes) (problem : Problem) : Prop :=
  ∃ tokens, Tokenization bytes tokens ∧ ProblemTokens tokens problem

theorem Parses.unique {bytes left right} (first : Parses bytes left) (second : Parses bytes right) :
    left = right := by
  obtain ⟨tokens, tokenized, parsed⟩ := first
  obtain ⟨otherTokens, otherTokenized, otherParsed⟩ := second
  have same := tokenized.unique otherTokenized
  subst otherTokens
  exact parsed.unique otherParsed

/- Source meaning is supplied by the declarative byte/token grammar and named
   first-order semantics. It does not depend on either executable parser. -/
def BytesSatisfiable (bytes : Bytes) : Prop :=
  ∃ problem, Parses bytes problem ∧ Source.Satisfiable problem

theorem original_bytes_unsat_of_witness {bytes problem signature symbols encoded}
    (parsed : Parses bytes problem)
    (encoding : ProblemEncoding signature symbols problem encoded)
    (certificate : Fang.Certificate)
    (accepted : Fang.check (Fang.preprocess encoded) certificate = true) :
    ¬ BytesSatisfiable bytes := by
  rintro ⟨other, otherParsed, satisfiable⟩
  have equal := parsed.unique otherParsed
  subst other
  exact encoding.unsat_of_check certificate accepted satisfiable

#print axioms MaximalPrefix.unique
#print axioms WordSpelling.unique
#print axioms Lexeme.unique
#print axioms Parses.unique
#print axioms original_bytes_unsat_of_witness

end Fang.Source.Grammar
