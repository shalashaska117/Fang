/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import AnnotationLexer
import Fang.SourceAsciiValidity

namespace Fang.TstpText

open Source.Grammar

def sourceToken : Source.Grammar.Token → TstpUnique.Token
  | .lower name => .atom name
  | .variable name => .variable name
  | .falseLiteral => .falseLiteral
  | .lparen => .punctuation '('
  | .rparen => .punctuation ')'
  | .comma => .punctuation ','
  | .period => .punctuation '.'
  | .disjoin => .punctuation '|'
  | .negate => .punctuation '~'

theorem spelling_chars (name : String) (ascii : ∀ b ∈ spelling name, b.toNat < 128) :
    (spelling name).map byteChar = name.toList := by
  have same : String.ofList ((spelling name).map byteChar) = name :=
    spelling_injective (ascii_string_of_bytes _ ascii)
  simpa using congrArg String.toList same

theorem word_character {b : UInt8} (word : IsWord b) :
    Frontend.wordChar (byteChar b) = true := by
  apply (wordChar_iff _ (byteChar_ascii b word.ascii)).mpr
  simpa [asciiByte_byteChar b word.ascii] using word

theorem space_character {b : UInt8} (space : IsSpace b) :
    Frontend.asciiSpace (byteChar b) = true := by
  apply (asciiSpace_iff _ (byteChar_ascii b space.ascii)).mpr
  simpa [asciiByte_byteChar b space.ascii] using space

theorem word_spelling_classified {bytes token} (word : WordSpelling bytes token) :
    TstpUnique.classifyWord (bytes.map byteChar) = some (sourceToken token) := by
  cases word with
  | lower name text valid =>
    subst bytes
    rw [spelling_chars name (WordSpelling.ascii (.lower name rfl valid))]
    exact (TstpUnique.lower_word name valid).2.2
  | variableWord name text valid =>
    subst bytes
    have ascii := string_ascii_of_spelling name (WordSpelling.ascii (.variableWord name rfl valid))
    have upper := (Frontend.variableName_iff name ascii).mpr valid
    have lower : Frontend.lowerName name = false := by
      cases checked : Frontend.lowerName name with
      | false => rfl
      | true => exact False.elim (name_kinds_disjoint ((Frontend.lowerName_iff name ascii).mp checked) valid)
    rw [spelling_chars name (WordSpelling.ascii (.variableWord name rfl valid))]
    simp [TstpUnique.classifyWord, sourceToken, lower, upper]
  | falsity text =>
    subst bytes
    decide

theorem extended_word_boundary {rest : Bytes} (ascii : ∀ b ∈ rest, b.toNat < 128)
    (boundary : ∀ b tail, rest = b :: tail → ¬ IsWord b)
    (suffix : List Char) (suffixBoundary : TstpUnique.WordBoundary suffix) :
    TstpUnique.WordBoundary (rest.map byteChar ++ suffix) := by
  cases rest with
  | nil => exact suffixBoundary
  | cons b bytes =>
    intro c tail eq
    have same := (List.cons.inj eq).1
    subst c
    have notWord := boundary b bytes rfl
    cases checked : Frontend.wordChar (byteChar b) with
    | false => rfl
    | true =>
      have word := (wordChar_iff _ (byteChar_ascii b (ascii b (by simp)))).mp checked
      exact False.elim (notWord (by simpa [asciiByte_byteChar b (ascii b (by simp))] using word))

theorem source_lexeme {bytes token rest}
    (lexeme : Source.Grammar.Lexeme bytes token rest)
    (ascii : ∀ b ∈ bytes, b.toNat < 128)
    (suffix : List Char) (boundary : TstpUnique.WordBoundary suffix) :
    TstpUnique.readToken (bytes.map byteChar ++ suffix) =
      some (sourceToken token, rest.map byteChar ++ suffix) := by
  cases lexeme with
  | word shape maximal word =>
    rename_i front
    rw [shape, List.map_append, List.append_assoc]
    have restAscii : ∀ b ∈ rest, b.toNat < 128 := by
      intro b member
      exact ascii b (by rw [shape]; exact List.mem_append_right _ member)
    apply TstpUnique.readToken_word
    · simpa using word.word_bytes.1
    · intro c member
      obtain ⟨b, present, rfl⟩ := List.mem_map.mp member
      exact word_character (word.word_bytes.2 b present)
    · exact extended_word_boundary restAscii maximal.boundary suffix boundary
    · exact word_spelling_classified word
  | punctuation spelled =>
    cases spelled <;>
      simpa [sourceToken, byteChar] using
        TstpUnique.readToken_punctuation _ (by simp [TstpUnique.punctuation]) (rest.map byteChar ++ suffix)

/-- A finite prefix of calls to the independent deterministic lexer. Whitespace
may occur before a token or at the end of the source slice. -/
inductive SourcePrefix : List Char → List TstpUnique.Token → List Char → Prop where
  | empty (rest : List Char) : SourcePrefix rest [] rest
  | whitespace {c input tokens rest} (space : Frontend.asciiSpace c = true)
      (tail : SourcePrefix input tokens rest) : SourcePrefix (c :: input) tokens rest
  | token {input token middle tokens rest}
      (read : TstpUnique.readToken input = some (token, middle))
      (tail : SourcePrefix middle tokens rest) : SourcePrefix input (token :: tokens) rest

theorem source_tokenization {bytes tokens} (lexical : Source.Grammar.Tokenization bytes tokens)
    (suffix : List Char) (boundary : TstpUnique.WordBoundary suffix) :
    SourcePrefix (bytes.map byteChar ++ suffix) (tokens.map sourceToken) suffix := by
  induction lexical with
  | empty => exact .empty suffix
  | whitespace space tail ih =>
    exact .whitespace (space_character space) ih
  | token lexeme tail ih =>
    exact .token (source_lexeme lexeme (lexeme.ascii tail.ascii) suffix boundary) ih

theorem readToken_space (c : Char) (space : Frontend.asciiSpace c = true) (rest : List Char) :
    TstpUnique.readToken (c :: rest) = TstpUnique.readToken rest := by
  simp [TstpUnique.readToken, List.dropWhile, space]

theorem SourcePrefix.head {input token tokens rest}
    (h : SourcePrefix input (token :: tokens) rest) :
    ∃ middle, TstpUnique.readToken input = some (token, middle) ∧
      SourcePrefix middle tokens rest := by
  cases h with
  | whitespace space tail =>
    obtain ⟨middle, read, remaining⟩ := SourcePrefix.head tail
    exact ⟨middle, (readToken_space _ space _).trans read, remaining⟩
  | token read tail => exact ⟨_, read, tail⟩
termination_by input.length

theorem SourcePrefix.empty_read {input rest} (h : SourcePrefix input [] rest) :
    TstpUnique.readToken input = TstpUnique.readToken rest := by
  cases h with
  | empty => rfl
  | whitespace space tail => exact (readToken_space _ space _).trans tail.empty_read
termination_by input.length

theorem sourceToken_not_lparen {token : Source.Grammar.Token} (h : token ≠ .lparen) :
    sourceToken token ≠ .punctuation '(' := by
  cases token <;> simp_all [sourceToken]

end Fang.TstpText
