/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import QuotedAtom
import ClauseParsing

namespace Fang.TstpText

/-- The unsigned-integer token subset: either zero alone or a nonzero initial
digit followed by decimal digits. The numeral's value is stated separately. -/
structure NaturalSpelling (chars : List Char) (value : Nat) : Prop where
  digits : ∀ c ∈ chars, 48 ≤ c.toNat ∧ c.toNat ≤ 57
  leading : chars = ['0'] ∨ ∃ first rest,
    chars = first :: rest ∧ 49 ≤ first.toNat ∧ first.toNat ≤ 57
  value : Nat.ofDigitChars 10 chars 0 = value

theorem decimal_digit {index : Nat} {c : Char} (present : c ∈ Nat.toDigits 10 index) :
    48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  apply (Source.Grammar.asciiDigit_nat c).mp
  simpa [Char.isDigit, Frontend.asciiDigit, Char.le_def] using
    Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) present

theorem decimal_positive_head (index : Nat) (positive : 0 < index) :
    ∃ first rest, Nat.toDigits 10 index = first :: rest ∧ first ≠ '0' := by
  induction index using Nat.strongRecOn with
  | ind index ih =>
    by_cases small : index < 10
    · refine ⟨index.digitChar, [], Nat.toDigits_of_lt_base small, ?_⟩
      intro zero
      have := Nat.digitChar_eq_zero.mp zero
      omega
    · have smaller : index / 10 < index := Nat.div_lt_self positive (by decide)
      have quotientPositive : 0 < index / 10 := by omega
      obtain ⟨first, rest, shape, nonzero⟩ := ih (index / 10) smaller quotientPositive
      refine ⟨first, rest ++ [(index % 10).digitChar], ?_, nonzero⟩
      rw [Nat.toDigits_of_base_le (by decide) (by omega), shape]
      rfl

theorem natural_spelling (index : Nat) : NaturalSpelling (toString index).toList index := by
  have characters : (toString index).toList = Nat.toDigits 10 index := by simp
  rw [characters]
  refine ⟨fun c present => decimal_digit present, ?_, by simp⟩
  by_cases zero : index = 0
  · subst index
    exact Or.inl (by simp)
  · obtain ⟨first, rest, shape, nonzero⟩ := decimal_positive_head index (by omega)
    have bounds := decimal_digit (index := index) (c := first) (by simp [shape])
    have notzero : first.toNat ≠ 48 := by
      intro same
      apply nonzero
      exact (Source.Grammar.char_eq_iff_nat _ _).mpr same
    exact Or.inr ⟨first, rest, shape, by omega, bounds.2⟩

theorem NaturalSpelling.functional {chars left right}
    (hl : NaturalSpelling chars left) (hr : NaturalSpelling chars right) : left = right :=
  hl.value.symm.trans hr.value

inductive AtomicText : String → String → Prop where
  | lower {name} (valid : Source.Grammar.LowerName name) : AtomicText name name
  | quoted {text name} (valid : QuotedAtom text.toList name.toList) : AtomicText text name

theorem checked_lower (name : String) (valid : Frontend.lowerName name = true) :
    AtomicText name name :=
  .lower ((Frontend.lowerName_iff name (Frontend.lowerName_ascii valid)).mp valid)

/-- Only the general-data constructors emitted by Fang. Formula data, colon
data, signed/reals and variables are outside this narrow annotation grammar. -/
inductive Datum where
  | atom : String → Datum
  | natural : Nat → Datum
  | function : String → List Datum → Datum
  | list : List Datum → Datum
  deriving Repr

mutual
inductive DataText : String → Datum → Prop where
  | atom {text name} (word : AtomicText text name) : DataText text (.atom name)
  | natural {text value} (number : NaturalSpelling text.toList value) :
      DataText text (.natural value)
  | function {nameText name texts values}
      (word : AtomicText nameText name) (nonempty : values ≠ [])
      (children : DataTexts texts values) :
      DataText (nameText ++ "(" ++ String.intercalate "," texts ++ ")") (.function name values)
  | list {texts values} (children : DataTexts texts values) :
      DataText ("[" ++ String.intercalate "," texts ++ "]") (.list values)
inductive DataTexts : List String → List Datum → Prop where
  | nil : DataTexts [] []
  | cons {text value texts values} (head : DataText text value)
      (tail : DataTexts texts values) : DataTexts (text :: texts) (value :: values)
end

theorem DataText.spelling_eq {left right : String} {value : Datum}
    (h : DataText left value) (same : left = right) : DataText right value := same ▸ h

macro "string_shape" : tactic =>
  `(tactic| (try simp only [String.intercalate_cons_cons, String.intercalate_singleton]
             apply String.toList_inj.mp
             simp only [String.toList_append, List.append_assoc]
             rfl))

theorem function_one (name : String) (valid : Frontend.lowerName name = true)
    {text value} (h : DataText text value) :
    DataText (name ++ "(" ++ text ++ ")") (.function name [value]) := by
  simpa using DataText.function (checked_lower name valid) (by simp) (.cons h .nil)

theorem function_two (name : String) (valid : Frontend.lowerName name = true)
    {first left second right} (h₁ : DataText first left) (h₂ : DataText second right) :
    DataText (name ++ "(" ++ first ++ "," ++ second ++ ")") (.function name [left, right]) := by
  simpa [String.append_assoc] using
    DataText.function (checked_lower name valid) (by simp) (.cons h₁ (.cons h₂ .nil))

theorem function_three (name : String) (valid : Frontend.lowerName name = true)
    {first left second middle third right}
    (h₁ : DataText first left) (h₂ : DataText second middle) (h₃ : DataText third right) :
    DataText (name ++ "(" ++ first ++ "," ++ second ++ "," ++ third ++ ")")
      (.function name [left, middle, right]) := by
  simpa [String.append_assoc] using
    DataText.function (checked_lower name valid) (by simp) (.cons h₁ (.cons h₂ (.cons h₃ .nil)))

end Fang.TstpText
