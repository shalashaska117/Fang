/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The characters of an exported quantified equality formula. The lexemes are
   those of the version-7 lexer with two additions from TPTP: a lower word may
   hold upper-case letters after its first letter, and a single-quoted atom is
   one token. A text of space-separated tokens, each of which reads as itself,
   reads back as exactly that token list. -/
import EqualityQuantifiedLexing
import Product.NameSpelling

namespace Fang.QuantifiedEqualityTstp.FormulaLexing
open Frontend Source.Grammar EqualityFrontend QuantifiedEqualityFrontend TstpText

inductive FormulaLexeme : List Char → String → List Char → Prop where
  | lower {first heads rest} (head : SourceLower first) (maximal : MaximalPrefix SourceWord heads rest) :
      FormulaLexeme (first :: (heads ++ rest)) (String.ofList (first :: heads)) rest
  | upper {first heads rest} (head : SourceUpper first) (maximal : MaximalPrefix SourceWord heads rest) :
      FormulaLexeme (first :: (heads ++ rest)) (String.ofList (first :: heads)) rest
  | interpreted {heads rest} (maximal : MaximalPrefix SourceWord heads rest)
      (spelled : String.ofList ('$' :: heads) = "$false" ∨ String.ofList ('$' :: heads) = "$true") :
      FormulaLexeme ('$' :: (heads ++ rest)) (String.ofList ('$' :: heads)) rest
  | quoted {body payload rest} (nonempty : payload ≠ []) (atom : SqBody body payload) :
      FormulaLexeme ('\'' :: (body ++ '\'' :: rest)) (String.ofList ('\'' :: (body ++ ['\'']))) rest
  | implication (rest : List Char) : FormulaLexeme ('=' :: '>' :: rest) "=>" rest
  | disequality (rest : List Char) : FormulaLexeme ('!' :: '=' :: rest) "!=" rest
  | punctuation {character rest} (punctuation : QuantifiedEqualityPunctuation character)
      (allowed : SingleAllowed character rest) :
      FormulaLexeme (character :: rest) (String.singleton character) rest

inductive FormulaTokenization : List Char → List String → Prop where
  | empty : FormulaTokenization [] []
  | whitespace {character rest tokens} (space : RawSpace character)
      (tail : FormulaTokenization rest tokens) : FormulaTokenization (character :: rest) tokens
  | token {input text middle tokens} (read : FormulaLexeme input text middle)
      (tail : FormulaTokenization middle tokens) : FormulaTokenization input (text :: tokens)

/-- One lexeme read off the front of the characters. It is used only in proofs,
    to show that the relation reads a text in at most one way. -/
def readLexeme : List Char → Option (String × List Char)
  | [] => none
  | c :: cs =>
    if (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) then
      some (String.ofList (c :: (cs.span sourceWordChar).1), (cs.span sourceWordChar).2)
    else if c = '$' then
      some (String.ofList ('$' :: (cs.span sourceWordChar).1), (cs.span sourceWordChar).2)
    else if c = '\'' then
      (quoteClose '\'' '\\' cs).map fun found => (String.ofList ('\'' :: found.1), found.2)
    else if c = '=' ∧ cs.head? = some '>' then some ("=>", cs.drop 1)
    else if c = '!' ∧ cs.head? = some '=' then some ("!=", cs.drop 1)
    else some (String.singleton c, cs)

theorem FormulaLexeme.read {input text rest} (lexeme : FormulaLexeme input text rest) :
    readLexeme input = some (text, rest) := by
  cases lexeme with
  | @lower first heads rest head maximal =>
    have span := source_span_eq rfl maximal
    have letter : (97 ≤ first.toNat ∧ first.toNat ≤ 122) ∨ (65 ≤ first.toNat ∧ first.toNat ≤ 90) := Or.inl head
    simp [readLexeme, letter, span]
  | @upper first heads rest head maximal =>
    have span := source_span_eq rfl maximal
    have letter : (97 ≤ first.toNat ∧ first.toNat ≤ 122) ∨ (65 ≤ first.toNat ∧ first.toNat ≤ 90) := Or.inr head
    simp [readLexeme, letter, span]
  | @interpreted heads rest maximal spelled =>
    have span := source_span_eq rfl maximal
    simp (config := { decide := true }) [readLexeme, span]
  | @quoted body payload rest nonempty atom =>
    have close := quoteClose_body charQuoteMap atom rest
    simp only [List.map_id] at close
    simp (config := { decide := true }) [readLexeme, close]
  | implication rest => simp (config := { decide := true }) [readLexeme]
  | disequality rest => simp (config := { decide := true }) [readLexeme]
  | punctuation punctuation allowed =>
    obtain ⟨equalStop, bangStop, _⟩ := allowed
    rcases punctuation with ordinary | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (config := { decide := true }) [readLexeme]
    all_goals simp_all (config := { decide := true }) [readLexeme]

theorem FormulaLexeme.unique {input left right leftRest rightRest}
    (first : FormulaLexeme input left leftRest) (second : FormulaLexeme input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  have pair := first.read.symm.trans second.read
  simp only [Option.some.injEq, Prod.mk.injEq] at pair
  exact pair

theorem FormulaLexeme.nonempty {input text rest} (lexeme : FormulaLexeme input text rest) : input ≠ [] := by
  intro empty
  subst empty
  have read := lexeme.read
  simp [readLexeme] at read

theorem FormulaLexeme.head_not_space {input text rest} (lexeme : FormulaLexeme input text rest)
    {character : Char} {tail : List Char} (shape : input = character :: tail) : ¬ RawSpace character := by
  intro space
  have spaced := (asciiSpace_raw character).mpr space
  cases lexeme with
  | lower head _ | upper head _ =>
    obtain ⟨rfl, -⟩ := List.cons.inj shape
    simp only [asciiSpace, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
      char_eq_iff_nat] at spaced
    simp only [SourceLower, SourceUpper] at head
    have : (' ' : Char).toNat = 32 := rfl
    omega
  | interpreted | quoted | implication | disequality =>
    obtain ⟨rfl, -⟩ := List.cons.inj shape
    revert spaced
    decide
  | punctuation punctuation =>
    obtain ⟨rfl, -⟩ := List.cons.inj shape
    simp [(punctuation_classes punctuation).1] at spaced

theorem FormulaTokenization.unique {input left right}
    (first : FormulaTokenization input left) (second : FormulaTokenization input right) : left = right := by
  induction first generalizing right with
  | empty =>
    cases second with
    | empty => rfl
    | token read _ => exact False.elim (read.nonempty rfl)
  | whitespace space tail induction =>
    cases second with
    | whitespace other otherTail => exact induction otherTail
    | token read _ => exact False.elim (read.head_not_space rfl space)
  | token read rest induction =>
    cases second with
    | empty => exact False.elim (read.nonempty rfl)
    | whitespace space _ => exact False.elim (read.head_not_space rfl space)
    | token other otherRest =>
      obtain ⟨tokenEqual, restEqual⟩ := read.unique other
      subst restEqual
      have tailsEqual := induction otherRest
      cases tokenEqual; cases tailsEqual
      rfl

theorem FormulaLexeme.ascii {input text rest} (lexeme : FormulaLexeme input text rest)
    (restAscii : ∀ c ∈ rest, c.toNat < 128) : ∀ c ∈ input, c.toNat < 128 := by
  intro c member
  cases lexeme with
  | lower head maximal | upper head maximal =>
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with rfl | inside | later
    · simp only [SourceLower, SourceUpper] at head
      omega
    · exact sourceWord_ascii (maximal.members c inside)
    · exact restAscii c later
  | interpreted maximal =>
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with rfl | inside | later
    · decide
    · exact sourceWord_ascii (maximal.members c inside)
    · exact restAscii c later
  | quoted nonempty atom =>
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with rfl | inside | rfl | later
    · decide
    · have bound := atom.printable c inside
      omega
    · decide
    · exact restAscii c later
  | implication | disequality =>
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | later
    · decide
    · decide
    · exact restAscii c later
  | punctuation punctuation =>
    rcases List.mem_cons.mp member with rfl | later
    · exact (punctuation_classes punctuation).2.2.2
    · exact restAscii c later

theorem FormulaTokenization.ascii {input tokens} (tokenized : FormulaTokenization input tokens) :
    ∀ c ∈ input, c.toNat < 128 := by
  induction tokenized with
  | empty => simp
  | whitespace space _ ih =>
    intro c member
    rcases List.mem_cons.mp member with rfl | later
    · exact space.1
    · exact ih c later
  | token read _ ih => exact read.ascii ih

/-- Formula characters spelled by bytes. -/
def FormulaByteTokenization (bytes : List UInt8) (tokens : List String) : Prop :=
  ∃ characters, FormulaTokenization characters tokens ∧ characters.map asciiByte = bytes

theorem FormulaByteTokenization.unique {bytes left right}
    (first : FormulaByteTokenization bytes left) (second : FormulaByteTokenization bytes right) :
    left = right := by
  obtain ⟨firstChars, first, firstBytes⟩ := first
  obtain ⟨secondChars, second, secondBytes⟩ := second
  have same : String.ofList firstChars = String.ofList secondChars := by
    apply spelling_injective
    exact (spelling_ofList_ascii _ first.ascii).trans
      (firstBytes.trans (secondBytes.symm.trans (spelling_ofList_ascii _ second.ascii).symm))
  have chars := congrArg String.toList same
  simp only [String.toList_ofList] at chars
  subst secondChars
  exact first.unique second

/-! A printed token list reads back as itself. -/

/-- A token that reads as itself when a space or nothing follows it. -/
def Standalone (text : String) : Prop :=
  ∀ rest : List Char, (∀ c tail, rest = c :: tail → c = ' ') → FormulaLexeme (text.toList ++ rest) text rest

theorem space_boundary {rest : List Char} (after : ∀ c tail, rest = c :: tail → c = ' ') :
    ∀ item tail, rest = item :: tail → ¬ SourceWord item := by
  intro item tail same word
  have space := after item tail same
  subst space
  simp only [SourceWord, SourceLower, SourceUpper] at word
  revert word
  decide

theorem intercalate_tokenization : ∀ tokens : List String, (∀ token ∈ tokens, Standalone token) →
    FormulaTokenization (String.intercalate " " tokens).toList tokens
  | [], _ => by simpa using FormulaTokenization.empty
  | [token], valid => by
    have read := valid token (by simp) [] (by intro c tail same; cases same)
    simpa using FormulaTokenization.token read .empty
  | token :: next :: rest, valid => by
    have tail := intercalate_tokenization (next :: rest) (fun other member => valid other (by simp [member]))
    have read := valid token (by simp) (' ' :: (String.intercalate " " (next :: rest)).toList)
      (by intro c tail same; exact (List.cons.inj same).1.symm)
    have whole := FormulaTokenization.token read (.whitespace ((asciiSpace_raw ' ').mp rfl) tail)
    rw [String.intercalate_cons_cons]
    have spaceChars : " ".toList = [' '] := rfl
    simpa only [String.toList_append, spaceChars, List.append_assoc, List.cons_append, List.nil_append]
      using whole

theorem standalone_single {character : Char} {text : String} (same : text = String.singleton character)
    (punctuation : QuantifiedEqualityPunctuation character) : Standalone text := by
  subst same
  intro rest after
  have allowed : SingleAllowed character rest := by
    cases rest with
    | nil => simp [SingleAllowed]
    | cons head tail =>
      have space := after head tail rfl
      subst space
      simp [SingleAllowed]
  simpa using FormulaLexeme.punctuation punctuation allowed

theorem standalone_implication : Standalone "=>" := by
  intro rest _
  exact FormulaLexeme.implication rest

theorem standalone_disequality : Standalone "!=" := by
  intro rest _
  exact FormulaLexeme.disequality rest

theorem standalone_truth : Standalone "$true" := by
  intro rest after
  have maximal : MaximalPrefix SourceWord ['t', 'r', 'u', 'e'] rest := by
    refine ⟨fun item member => ?_, space_boundary after⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> (simp only [SourceWord, SourceLower, SourceUpper]; decide)
  exact FormulaLexeme.interpreted maximal (Or.inr (by decide))

theorem standalone_falsity : Standalone "$false" := by
  intro rest after
  have maximal : MaximalPrefix SourceWord ['f', 'a', 'l', 's', 'e'] rest := by
    refine ⟨fun item member => ?_, space_boundary after⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> (simp only [SourceWord, SourceLower, SourceUpper]; decide)
  exact FormulaLexeme.interpreted maximal (Or.inl (by decide))

theorem standalone_open : Standalone "(" := standalone_single (character := '(') rfl (by simp [QuantifiedEqualityPunctuation, RawPunctuation])
theorem standalone_close : Standalone ")" := standalone_single (character := ')') rfl (by simp [QuantifiedEqualityPunctuation, RawPunctuation])
theorem standalone_comma : Standalone "," := standalone_single (character := ',') rfl (by simp [QuantifiedEqualityPunctuation, RawPunctuation])
theorem standalone_equal : Standalone "=" := standalone_single (character := '=') rfl (by simp [QuantifiedEqualityPunctuation])
theorem standalone_and : Standalone "&" := standalone_single (character := '&') rfl (by simp [QuantifiedEqualityPunctuation])
theorem standalone_or : Standalone "|" := standalone_single (character := '|') rfl (by simp [QuantifiedEqualityPunctuation, RawPunctuation])
theorem standalone_not : Standalone "~" := standalone_single (character := '~') rfl (by simp [QuantifiedEqualityPunctuation, RawPunctuation])
theorem standalone_all : Standalone "!" := standalone_single (character := '!') rfl (by simp [QuantifiedEqualityPunctuation])
theorem standalone_ex : Standalone "?" := standalone_single (character := '?') rfl (by simp [QuantifiedEqualityPunctuation])
theorem standalone_lbracket : Standalone "[" := standalone_single (character := '[') rfl (by simp [QuantifiedEqualityPunctuation])
theorem standalone_rbracket : Standalone "]" := standalone_single (character := ']') rfl (by simp [QuantifiedEqualityPunctuation])
theorem standalone_colon : Standalone ":" := standalone_single (character := ':') rfl (by simp [QuantifiedEqualityPunctuation])

/-- The characters of a word whose first byte and following bytes have the given classes. -/
theorem word_chars {name : String} {byte : UInt8} {bytes : Bytes} (shape : spelling name = byte :: bytes)
    (ascii : ∀ b ∈ byte :: bytes, b.toNat < 128) :
    ∃ first rest, name.toList = first :: rest ∧ first.toNat = byte.toNat ∧
      ∀ c ∈ rest, ∃ b ∈ bytes, c.toNat = b.toNat := by
  have charsAscii : ∀ c ∈ name.toList, c.toNat < 128 := by
    apply string_ascii_of_spelling
    rw [shape]
    exact ascii
  have encoded := spelling_ascii name charsAscii
  rw [shape] at encoded
  cases chars : name.toList with
  | nil => rw [chars] at encoded; simp at encoded
  | cons first rest =>
    rw [chars] at encoded
    simp only [List.map_cons, List.cons.injEq] at encoded
    obtain ⟨headByte, tailBytes⟩ := encoded
    refine ⟨first, rest, rfl, ?_, ?_⟩
    · rw [headByte, asciiByte_value first (charsAscii first (by simp [chars]))]
    · intro c member
      refine ⟨asciiByte c, by rw [tailBytes]; exact List.mem_map.mpr ⟨c, member, rfl⟩, ?_⟩
      rw [asciiByte_value c (charsAscii c (by simp [chars, member]))]

theorem standalone_variable {name : String} (valid : VariableName name) : Standalone name := by
  obtain ⟨byte, bytes, shape, upper, tail⟩ := valid
  have ascii : ∀ b ∈ byte :: bytes, b.toNat < 128 := by
    intro b member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [IsUpper] at upper
      omega
    · rcases tail b member with h | h | h | h <;> (try simp only [IsLower, IsUpper, IsDigit] at h) <;> omega
  obtain ⟨first, rest, chars, firstValue, restValues⟩ := word_chars shape ascii
  intro after following
  have head : SourceUpper first := by
    simp only [SourceUpper, IsUpper] at upper ⊢
    omega
  have members : ∀ c ∈ rest, SourceWord c := by
    intro c member
    obtain ⟨b, bMember, value⟩ := restValues c member
    have kind := tail b bMember
    simp only [IsLower, IsUpper, IsDigit] at kind
    simp only [SourceWord, SourceLower, SourceUpper]
    omega
  have lexeme := FormulaLexeme.upper (rest := after) head ⟨members, space_boundary following⟩
  rw [← chars, String.ofList_toList] at lexeme
  simpa [chars] using lexeme

theorem standalone_lower {name : String} (valid : LowerWord name) : Standalone name := by
  obtain ⟨byte, bytes, shape, lower, tail⟩ := valid
  have ascii : ∀ b ∈ byte :: bytes, b.toNat < 128 := by
    intro b member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [IsLower] at lower
      omega
    · rcases tail b member with h | h | h | h <;> (try simp only [IsLower, IsUpper, IsDigit] at h) <;> omega
  obtain ⟨first, rest, chars, firstValue, restValues⟩ := word_chars shape ascii
  intro after following
  have head : SourceLower first := by
    simp only [SourceLower, IsLower] at lower ⊢
    omega
  have members : ∀ c ∈ rest, SourceWord c := by
    intro c member
    obtain ⟨b, bMember, value⟩ := restValues c member
    have kind := tail b bMember
    simp only [IsLower, IsUpper, IsDigit] at kind
    simp only [SourceWord, SourceLower, SourceUpper]
    omega
  have lexeme := FormulaLexeme.lower (rest := after) head ⟨members, space_boundary following⟩
  rw [← chars, String.ofList_toList] at lexeme
  simpa [chars] using lexeme

theorem standalone_quoted {text : String} {payload : List Char} (valid : QuotedAtom text.toList payload) :
    Standalone text := by
  intro after _
  generalize chars : text.toList = code at valid
  cases valid with
  | @atom bodyChars _ nonempty body =>
    have lexeme := FormulaLexeme.quoted (rest := after) nonempty body
    have same : String.ofList ('\'' :: (bodyChars ++ ['\''])) = text := by
      apply String.toList_inj.mp
      simp [chars]
    rw [same] at lexeme
    simpa [chars] using lexeme

theorem standalone_atomic {text name : String} (word : AtomicText text name) : Standalone text := by
  cases word with
  | lower valid => exact standalone_lower valid
  | quoted valid => exact standalone_quoted valid

#print axioms Fang.QuantifiedEqualityTstp.FormulaLexing.FormulaLexeme.unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaLexing.FormulaTokenization.unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaLexing.FormulaByteTokenization.unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaLexing.intercalate_tokenization
#print axioms Fang.QuantifiedEqualityTstp.FormulaLexing.standalone_atomic

end Fang.QuantifiedEqualityTstp.FormulaLexing
