/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import AnnotationGrammar
import Fang.SourceAsciiValidity

namespace Fang.TstpUnique
open Fang.TstpText

inductive Token where
  | atom : String → Token
  | natural : Nat → Token
  | variable : String → Token
  | falseLiteral : Token
  | punctuation : Char → Token
  deriving DecidableEq, Repr

def punctuation : List Char := ['(', ')', ',', '.', '[', ']', '~', '|']

/-- Scan one quoted body, consuming its closing quote and preserving the suffix. -/
def readQuotedBody : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c = '\'' then some ([], rest)
    else if c = '\\' then
      match rest with
      | [] => none
      | escaped :: tail =>
        if escaped = '\'' ∨ escaped = '\\' then do
          let (payload, suffix) ← readQuotedBody tail
          some (escaped :: payload, suffix)
        else none
    else if 32 ≤ c.toNat ∧ c.toNat ≤ 126 then do
      let (payload, suffix) ← readQuotedBody rest
      some (c :: payload, suffix)
    else none

theorem readQuotedBody_correct {code payload : List Char} (grammar : SqBody code payload)
    (suffix : List Char) :
    readQuotedBody (code ++ '\'' :: suffix) = some (payload, suffix) := by
  induction grammar with
  | nil =>
    simp only [List.nil_append]
    rw [readQuotedBody.eq_def]
    simp
  | cons head tail ih =>
    cases head with
    | plain c lo hi quote slash =>
      simp only [List.cons_append, List.nil_append]
      rw [readQuotedBody.eq_def]
      simp [quote, slash, lo, hi, ih]
    | quote => simp [readQuotedBody, ih]
    | slash => simp [readQuotedBody, ih]

def canonicalNatural (chars : List Char) : Bool :=
  !chars.isEmpty && chars.all Frontend.asciiDigit &&
    (chars == ['0'] || chars.head? != some '0')

def classifyWord (chars : List Char) : Option Token :=
  let name := String.ofList chars
  if Frontend.lowerName name then some (.atom name)
  else if Frontend.variableName name then some (.variable name)
  else if canonicalNatural chars then some (.natural (Nat.ofDigitChars 10 chars 0))
  else if name = "$false" then some .falseLiteral
  else none

def readBareToken : List Char → Option (Token × List Char)
  | [] => none
  | c :: rest =>
    if c = '\'' then do
      let (payload, suffix) ← readQuotedBody rest
      if payload.isEmpty then none else some (.atom (String.ofList payload), suffix)
    else if Frontend.wordChar c then
      let (front, suffix) := (c :: rest).span Frontend.wordChar
      do
        let token ← classifyWord front
        some (token, suffix)
    else if punctuation.contains c then some (.punctuation c, rest)
    else none

def readToken (input : List Char) : Option (Token × List Char) :=
  readBareToken (input.dropWhile Frontend.asciiSpace)

theorem span_prefix (predicate : Char → Bool) (front suffix : List Char)
    (members : ∀ c ∈ front, predicate c = true)
    (boundary : ∀ c rest, suffix = c :: rest → predicate c = false) :
    (front ++ suffix).span predicate = (front, suffix) := by
  have scanned := Frontend.span_spec predicate (front ++ suffix)
  have given : Source.Grammar.MaximalPrefix (fun c => predicate c = true) front suffix :=
    ⟨members, fun c rest eq yes => by rw [boundary c rest eq] at yes; contradiction⟩
  obtain ⟨front_eq, suffix_eq⟩ := given.unique scanned.2 scanned.1
  exact Prod.ext front_eq.symm suffix_eq.symm

theorem word_not_quote_space (c : Char) (word : Frontend.wordChar c = true) :
    c ≠ '\'' ∧ Frontend.asciiSpace c = false := by
  constructor
  · intro eq
    subst c
    contradiction
  · cases hs : Frontend.asciiSpace c with
    | false => rfl
    | true => exact False.elim (Frontend.rawWord_not_space ((Frontend.wordChar_raw c).mp word)
        ((Frontend.asciiSpace_raw c).mp hs))

/-- A classified maximal word has one token and an exact, untouched remainder. -/
theorem readToken_word (front suffix : List Char) (token : Token) (nonempty : front ≠ [])
    (members : ∀ c ∈ front, Frontend.wordChar c = true)
    (boundary : ∀ c rest, suffix = c :: rest → Frontend.wordChar c = false)
    (classified : classifyWord front = some token) :
    readToken (front ++ suffix) = some (token, suffix) := by
  cases front with
  | nil => contradiction
  | cons c rest =>
    have word := members c List.mem_cons_self
    obtain ⟨notQuote, notSpace⟩ := word_not_quote_space c word
    have span := span_prefix Frontend.wordChar (c :: rest) suffix members boundary
    simp only [List.cons_append] at span
    simp [readToken, readBareToken, List.dropWhile, notQuote, notSpace, word, span, classified]

theorem readToken_quoted {code payload : List Char} (grammar : QuotedAtom code payload)
    (suffix : List Char) :
    readToken (code ++ suffix) = some (.atom (String.ofList payload), suffix) := by
  cases grammar with
  | atom nonempty body =>
    simp [readToken, readBareToken, List.dropWhile, List.append_assoc,
      readQuotedBody_correct body suffix, nonempty, Frontend.asciiSpace]

theorem readToken_punctuation (c : Char) (valid : c ∈ punctuation) (suffix : List Char) :
    readToken (c :: suffix) = some (.punctuation c, suffix) := by
  simp only [punctuation, List.mem_cons, List.not_mem_nil, or_false] at valid
  rcases valid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [readToken, readBareToken, List.dropWhile, Frontend.asciiSpace, Frontend.wordChar,
      Frontend.asciiLower, Frontend.asciiUpper, Frontend.asciiDigit, punctuation]

def WordBoundary (suffix : List Char) : Prop :=
  ∀ c rest, suffix = c :: rest → Frontend.wordChar c = false

theorem punctuation_boundary (c : Char) (valid : c ∈ punctuation) (suffix : List Char) :
    WordBoundary (c :: suffix) := by
  intro first rest eq
  have same := (List.cons.inj eq).1
  subst first
  simp only [punctuation, List.mem_cons, List.not_mem_nil, or_false] at valid
  rcases valid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem lower_word (name : String) (valid : Source.Grammar.LowerName name) :
    name.toList ≠ [] ∧ (∀ c ∈ name.toList, Frontend.wordChar c = true) ∧
      classifyWord name.toList = some (.atom name) := by
  have ascii := Source.Grammar.string_ascii_of_spelling name
    (Source.Grammar.WordSpelling.ascii (.lower name rfl valid))
  have checked := (Frontend.lowerName_iff name ascii).mpr valid
  constructor
  · intro empty
    simp [Frontend.lowerName, empty] at checked
  constructor
  · cases shape : name.toList with
    | nil => simp
    | cons first rest =>
      simp only [Frontend.lowerName, shape, Bool.and_eq_true, List.all_eq_true] at checked
      intro c member
      simp only [shape, List.mem_cons] at member
      rcases member with rfl | member
      · simp [Frontend.wordChar, checked.1]
      · have child := checked.2 c member
        simp only [Bool.or_eq_true] at child
        rcases child with (h | h) | h <;> simp [Frontend.wordChar, h]
  · simp [classifyWord, checked]

theorem readToken_atomic {text name : String} (grammar : AtomicText text name)
    (suffix : List Char) (boundary : WordBoundary suffix) :
    readToken (text.toList ++ suffix) = some (.atom name, suffix) := by
  cases grammar with
  | lower valid =>
    obtain ⟨nonempty, members, classified⟩ := lower_word text valid
    exact readToken_word text.toList suffix _ nonempty members boundary classified
  | quoted valid => simpa using readToken_quoted valid suffix

theorem natural_word {chars : List Char} {value : Nat} (valid : NaturalSpelling chars value) :
    chars ≠ [] ∧ (∀ c ∈ chars, Frontend.wordChar c = true) ∧
      classifyWord chars = some (.natural value) := by
  have nonempty : chars ≠ [] := by
    rcases valid.leading with zero | ⟨first, rest, shape, lo, hi⟩
    · simp [zero]
    · simp [shape]
  have digits : ∀ c ∈ chars, Frontend.asciiDigit c = true := by
    intro c member
    exact (Source.Grammar.asciiDigit_nat c).mpr (valid.digits c member)
  refine ⟨nonempty, ?_, ?_⟩
  · intro c member
    simp [Frontend.wordChar, digits c member]
  cases chars with
  | nil => contradiction
  | cons first rest =>
    have bounds := valid.digits first List.mem_cons_self
    have lower : Frontend.asciiLower first = false := by
      cases checked : Frontend.asciiLower first with
      | false => rfl
      | true => have bad := (Source.Grammar.asciiLower_nat first).mp checked; omega
    have upper : Frontend.asciiUpper first = false := by
      cases checked : Frontend.asciiUpper first with
      | false => rfl
      | true => have bad := (Source.Grammar.asciiUpper_nat first).mp checked; omega
    have leading : (first :: rest == ['0']) = true ∨ first ≠ '0' := by
      rcases valid.leading with zero | ⟨head, tail, shape, lo, hi⟩
      · exact Or.inl (by simp [zero])
      · have same := (List.cons.inj shape).1
        subst head
        right
        intro eq
        subst first
        contradiction
    have canonical : canonicalNatural (first :: rest) = true := by
      have allDigits := List.all_eq_true.mpr digits
      rcases leading with zero | nonzero <;>
        simp [canonicalNatural, allDigits, *]
    simp [classifyWord, Frontend.lowerName, Frontend.variableName, lower, upper,
      canonical, valid.value]

theorem readToken_natural {text : String} {value : Nat}
    (grammar : NaturalSpelling text.toList value)
    (suffix : List Char) (boundary : WordBoundary suffix) :
    readToken (text.toList ++ suffix) = some (.natural value, suffix) := by
  obtain ⟨nonempty, members, classified⟩ := natural_word grammar
  exact readToken_word text.toList suffix _ nonempty members boundary classified

end Fang.TstpUnique
