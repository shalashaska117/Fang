/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import AnnotationParser

namespace Fang.TstpUnique
open Fang.TstpText

inductive DataBoundary : List Char → Prop where
  | empty : DataBoundary []
  | comma (suffix : List Char) : DataBoundary (',' :: suffix)
  | paren (suffix : List Char) : DataBoundary (')' :: suffix)
  | bracket (suffix : List Char) : DataBoundary (']' :: suffix)

theorem DataBoundary.word {suffix} (valid : DataBoundary suffix) : WordBoundary suffix := by
  cases valid with
  | empty => intro c rest impossible; contradiction
  | comma tail => exact punctuation_boundary ',' (by decide) tail
  | paren tail => exact punctuation_boundary ')' (by decide) tail
  | bracket tail => exact punctuation_boundary ']' (by decide) tail

theorem DataBoundary.noArguments {suffix} (valid : DataBoundary suffix) (rest : List Char) :
    readToken suffix ≠ some (.punctuation '(', rest) := by
  cases valid with
  | empty => simp [readToken, readBareToken]
  | comma tail => rw [readToken_punctuation ',' (by decide)]; simp
  | paren tail => rw [readToken_punctuation ')' (by decide)]; simp
  | bracket tail => rw [readToken_punctuation ']' (by decide)]; simp

theorem Closing.boundary (closing : Closing) (suffix : List Char) :
    DataBoundary (closing.char :: suffix) := by
  cases closing
  · exact .paren suffix
  · exact .bracket suffix

theorem Closing.punctuation (closing : Closing) : closing.char ∈ punctuation := by
  cases closing <;> decide

theorem DataTexts.empty {texts : List String} (grammar : DataTexts texts []) : texts = [] := by
  cases grammar
  rfl

mutual
theorem DataText.prefix {text : String} {value : Datum} (grammar : DataText text value)
    (suffix : List Char) (boundary : DataBoundary suffix) :
    ParsedData (text.toList ++ suffix) value suffix := by
  cases grammar with
  | atom word => exact .atom (readToken_atomic word suffix boundary.word) boundary.noArguments
  | natural number => exact .natural (readToken_natural number suffix boundary.word)
  | @function nameText name texts values word nonempty children =>
    have parsed := ParsedData.function
      (readToken_atomic word
        ('(' :: (String.intercalate "," texts).toList ++ ')' :: suffix)
        (punctuation_boundary '(' (by decide) _))
      (readToken_punctuation '(' (by decide) _)
      (DataTexts.prefix children nonempty .paren suffix)
    simpa [String.toList_append, List.append_assoc, Closing.char] using parsed
  | @list texts values children =>
    by_cases empty : values = []
    · subst values
      have textsEmpty := DataTexts.empty children
      subst texts
      simpa using ParsedData.emptyList
        (readToken_punctuation '[' (by decide) (']' :: suffix))
        (readToken_punctuation ']' (by decide) suffix)
    · have parsed := ParsedData.list
        (readToken_punctuation '[' (by decide)
          ((String.intercalate "," texts).toList ++ ']' :: suffix))
        (DataTexts.prefix children empty .bracket suffix)
      simpa [String.toList_append, List.append_assoc, Closing.char] using parsed

theorem DataTexts.prefix {texts : List String} {values : List Datum}
    (grammar : DataTexts texts values) (nonempty : values ≠ [])
    (closing : Closing) (suffix : List Char) :
    ParsedItems ((String.intercalate "," texts).toList ++ closing.char :: suffix)
      values suffix closing := by
  cases grammar with
  | nil => contradiction
  | @cons text value texts values head tail =>
    by_cases empty : values = []
    · subst values
      have textsEmpty := DataTexts.empty tail
      subst texts
      simpa using ParsedItems.last
        (DataText.prefix head (closing.char :: suffix) (closing.boundary suffix))
        (readToken_punctuation closing.char closing.punctuation suffix)
    · have textNonempty : texts ≠ [] := by
        intro bad
        subst texts
        cases tail
        contradiction
      have parsed := ParsedItems.more
        (DataText.prefix head
          (',' :: (String.intercalate "," texts).toList ++ closing.char :: suffix)
          (.comma _))
        (readToken_punctuation ',' (by decide) _)
        (DataTexts.prefix tail empty closing suffix)
      simpa [String.intercalate_cons_of_ne_nil textNonempty, String.toList_append,
        List.append_assoc] using parsed
end

theorem DataText.functional {text : String} {left right : Datum}
    (first : DataText text left) (second : DataText text right) : left = right := by
  exact ((DataText.prefix first [] .empty).unique (DataText.prefix second [] .empty)).1

end Fang.TstpUnique
