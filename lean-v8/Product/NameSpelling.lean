/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Product.QuotedAtom
import Fang.FrontendTokenView
import Fang.SourceAsciiValidity

/-! TPTP atomic words as the exporters print them. A symbol name is printed as
a lower word when it is one and as a single-quoted atom otherwise. This module
states both forms as grammar relations, independent of the printer, and proves
that the printer's text has the form it claims. -/

namespace Fang.TstpText

open Source.Grammar

/-- TPTP's `lower_word` over bytes: a lower-case letter, then letters, digits and underscores. -/
def LowerWord (name : String) : Prop :=
  ∃ first rest, spelling name = first :: rest ∧ IsLower first ∧
    ∀ byte ∈ rest, IsLower byte ∨ IsUpper byte ∨ IsDigit byte ∨ byte.toNat = 95

theorem LowerWord.of_name {name : String} (valid : LowerName name) : LowerWord name := by
  obtain ⟨first, rest, shape, head, tail⟩ := valid
  refine ⟨first, rest, shape, head, fun byte member => ?_⟩
  rcases tail byte member with lower | digit | underscore
  · exact Or.inl lower
  · exact Or.inr (Or.inr (Or.inl digit))
  · exact Or.inr (Or.inr (Or.inr underscore))

/-- A nonempty name of printable ASCII bytes. -/
def PrintableName (name : String) : Prop :=
  spelling name ≠ [] ∧ ∀ byte ∈ spelling name, 32 ≤ byte.toNat ∧ byte.toNat ≤ 126

/-- An atomic word and the name it denotes: a lower word denotes itself and a
single-quoted atom its decoded content. -/
inductive AtomicText : String → String → Prop where
  | lower {name} (valid : LowerWord name) : AtomicText name name
  | quoted {text name} (valid : QuotedAtom text.toList name.toList) : AtomicText text name

/-! The printer's classification. -/

theorem lowerWord_ascii {name : String} (valid : TstpExport.lowerWord name = true) :
    ∀ character ∈ name.toList, character.toNat < 128 := by
  cases shape : name.toList with
  | nil => simp [TstpExport.lowerWord, shape] at valid
  | cons first rest =>
    simp only [TstpExport.lowerWord, shape, Bool.and_eq_true, List.all_eq_true] at valid
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · have bound := (asciiLower_nat character).mp valid.1
      omega
    · have chosen := valid.2 character member
      simp only [Bool.or_eq_true, beq_iff_eq] at chosen
      rcases chosen with ((lower | upper) | digit) | same
      · have bound := (asciiLower_nat character).mp lower
        omega
      · have bound := (asciiUpper_nat character).mp upper
        omega
      · have bound := (asciiDigit_nat character).mp digit
        omega
      · subst character
        decide

theorem lowerWord_word {name : String} (valid : TstpExport.lowerWord name = true) : LowerWord name := by
  have ascii := lowerWord_ascii valid
  have encoded := spelling_ascii name ascii
  cases shape : name.toList with
  | nil => simp [TstpExport.lowerWord, shape] at valid
  | cons first rest =>
    have firstAscii : first.toNat < 128 := ascii first (by simp [shape])
    have restAscii : ∀ character ∈ rest, character.toNat < 128 := by
      intro character member
      exact ascii character (by simp [shape, member])
    simp only [shape, List.map_cons] at encoded
    simp only [TstpExport.lowerWord, shape, Bool.and_eq_true, List.all_eq_true] at valid
    refine ⟨asciiByte first, rest.map asciiByte, encoded, (asciiLower_iff first firstAscii).mp valid.1, ?_⟩
    intro byte member
    obtain ⟨character, present, rfl⟩ := List.mem_map.mp member
    have tail := valid.2 character present
    exact (Frontend.variableTail_iff character (restAscii character present)).mp tail

theorem printableName_spec {name : String} (valid : TstpExport.printableName name = true) :
    PrintableName name := by
  simp only [TstpExport.printableName, Bool.and_eq_true, List.all_eq_true] at valid
  obtain ⟨nonempty, chars⟩ := valid
  have printable : ∀ c ∈ name.toList, 32 ≤ c.toNat ∧ c.toNat ≤ 126 := fun c member => by
    simpa using chars c member
  have ascii : ∀ c ∈ name.toList, c.toNat < 128 := fun c member => by
    have bound := printable c member
    omega
  have encoded := spelling_ascii name ascii
  refine ⟨?_, ?_⟩
  · rw [encoded]
    intro empty
    have blank : name.toList = [] := List.map_eq_nil_iff.mp empty
    have same : name = "" := by simpa using congrArg String.ofList blank
    subst name
    simp at nonempty
  · intro byte member
    rw [encoded] at member
    obtain ⟨c, present, rfl⟩ := List.mem_map.mp member
    rw [asciiByte_value c (ascii c present)]
    exact printable c present

/-- The characters of a printable name are printable. -/
theorem PrintableName.chars {name : String} (printable : PrintableName name) :
    name.toList ≠ [] ∧ ∀ c ∈ name.toList, 32 ≤ c.toNat ∧ c.toNat ≤ 126 := by
  have ascii := string_ascii_of_spelling name (fun byte member => by
    have bound := printable.2 byte member
    omega)
  have encoded := spelling_ascii name ascii
  refine ⟨fun empty => printable.1 (by rw [encoded, empty]; rfl), fun c member => ?_⟩
  have inBytes : asciiByte c ∈ spelling name := by
    rw [encoded]
    exact List.mem_map.mpr ⟨c, member, rfl⟩
  have bound := printable.2 _ inBytes
  rw [asciiByte_value c (ascii c member)] at bound
  exact bound

/-- The text `quoteText` builds is a quoted atom of the name. -/
theorem quoteText_grammar {name : String} (printable : PrintableName name) :
    QuotedAtom (TstpExport.quoteText name).toList name.toList := by
  have chars := printable.chars
  have body := quote_fold name.toList "" [] SqBody.nil chars.2
  simp only [List.nil_append] at body
  have grammar := QuotedAtom.atom chars.1 body
  simpa [TstpExport.quoteText, String.toList_append] using grammar

theorem symbolText_atomic {name : String} (printable : PrintableName name) :
    AtomicText (TstpExport.symbolText name) name := by
  by_cases lower : TstpExport.lowerWord name = true
  · simpa [TstpExport.symbolText, lower] using AtomicText.lower (lowerWord_word lower)
  · simpa [TstpExport.symbolText, lower] using AtomicText.quoted (quoteText_grammar printable)

/-! Facts about the two forms. -/

theorem SqChar.printable {code : List Char} {c : Char} (grammar : SqChar code c) :
    ∀ x ∈ code, 32 ≤ x.toNat ∧ x.toNat ≤ 126 := by
  cases grammar with
  | plain c lo hi => simp [lo, hi]
  | quote =>
    intro x member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  | slash =>
    intro x member
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
    subst x
    decide

theorem SqBody.printable {code payload : List Char} (grammar : SqBody code payload) :
    ∀ x ∈ code, 32 ≤ x.toNat ∧ x.toNat ≤ 126 := by
  induction grammar with
  | nil => simp
  | cons head _ ih =>
    intro x member
    rcases List.mem_append.mp member with here | later
    · exact head.printable x here
    · exact ih x later

theorem QuotedAtom.printable {code payload : List Char} (grammar : QuotedAtom code payload) :
    ∀ x ∈ code, 32 ≤ x.toNat ∧ x.toNat ≤ 126 := by
  cases grammar with
  | atom _ body =>
    intro x member
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
    rcases member with (rfl | inside) | rfl
    · decide
    · exact body.printable x inside
    · decide

theorem QuotedAtom.ascii {code payload : List Char} (grammar : QuotedAtom code payload) :
    ∀ x ∈ code, x.toNat < 128 := by
  intro x member
  have bound := grammar.printable x member
  omega

theorem QuotedAtom.head {code payload : List Char} (grammar : QuotedAtom code payload) :
    ∃ rest, code = '\'' :: rest := by
  cases grammar with
  | atom _ _ => exact ⟨_, rfl⟩

theorem quoted_spelling {text : String} {payload : List Char}
    (grammar : QuotedAtom text.toList payload) : ∃ rest, spelling text = 39 :: rest := by
  obtain ⟨rest, shape⟩ := grammar.head
  refine ⟨rest.map asciiByte, ?_⟩
  rw [spelling_ascii text grammar.ascii, shape]
  rfl

theorem lower_not_quoted {text : String} {payload : List Char} (lower : LowerWord text)
    (grammar : QuotedAtom text.toList payload) : False := by
  obtain ⟨first, rest, shape, head, _⟩ := lower
  obtain ⟨tail, spelled⟩ := quoted_spelling grammar
  have same := (List.cons.inj (shape.symm.trans spelled)).1
  subst first
  simp [IsLower] at head

theorem AtomicText.functional {text left right : String}
    (first : AtomicText text left) (second : AtomicText text right) : left = right := by
  cases first with
  | lower valid =>
    cases second with
    | lower => rfl
    | quoted quoted => exact (lower_not_quoted valid quoted).elim
  | quoted valid =>
    cases second with
    | lower other => exact (lower_not_quoted other valid).elim
    | quoted other => exact String.toList_inj.mp (QuotedAtom.functional valid other)

/-- The first byte of an atomic word is a lower-case letter or a quote. -/
theorem AtomicText.first {text name : String} (word : AtomicText text name) :
    ∃ first rest, spelling text = first :: rest ∧ (IsLower first ∨ first = 39) := by
  cases word with
  | lower valid =>
    obtain ⟨first, rest, shape, head, _⟩ := valid
    exact ⟨first, rest, shape, Or.inl head⟩
  | quoted valid =>
    obtain ⟨rest, shape⟩ := quoted_spelling valid
    exact ⟨39, rest, shape, Or.inr rfl⟩

theorem AtomicText.not_variable {text name : String} (word : AtomicText text name)
    (upperWord : VariableName text) : False := by
  obtain ⟨first, rest, shape, kind⟩ := word.first
  obtain ⟨other, others, otherShape, upper, _⟩ := upperWord
  have same := (List.cons.inj (shape.symm.trans otherShape)).1
  subst other
  simp only [IsLower, IsUpper] at kind upper
  rcases kind with lower | quote
  · omega
  · subst first
    simp at upper

/-! Where a quoted atom ends. A closing quote is the first quote that no
backslash escapes; `quoteClose` finds it. It is used only in proofs, to show
that the lexical grammars below read a quoted atom in exactly one way. -/

def quoteClose {α : Type} [DecidableEq α] (quote slash : α) : List α → Option (List α × List α)
  | [] => none
  | item :: rest =>
    if item = quote then some ([quote], rest)
    else if item = slash then
      match rest with
      | [] => none
      | escaped :: tail => (quoteClose quote slash tail).map fun found => (slash :: escaped :: found.1, found.2)
    else (quoteClose quote slash rest).map fun found => (item :: found.1, found.2)

def quotedPrefix {α : Type} [DecidableEq α] (quote slash : α) : List α → Option (List α × List α)
  | [] => none
  | item :: rest =>
    if item = quote then (quoteClose quote slash rest).map fun found => (quote :: found.1, found.2)
    else none

/-- A character map that keeps the quote and the backslash apart from every other printable character. -/
structure QuoteMap {α : Type} (f : Char → α) (quote slash : α) : Prop where
  atQuote : f '\'' = quote
  atSlash : f '\\' = slash
  onlyQuote : ∀ c, 32 ≤ c.toNat → c.toNat ≤ 126 → f c = quote → c = '\''
  onlySlash : ∀ c, 32 ≤ c.toNat → c.toNat ≤ 126 → f c = slash → c = '\\'

theorem QuoteMap.distinct {α : Type} {f : Char → α} {quote slash : α} (map : QuoteMap f quote slash) :
    slash ≠ quote := by
  intro same
  have wrong := map.onlyQuote '\\' (by decide) (by decide) (map.atSlash.trans same)
  exact absurd wrong (by decide)

theorem quoteClose_body {α : Type} [DecidableEq α] {f : Char → α} {quote slash : α}
    (map : QuoteMap f quote slash) {body payload : List Char} (grammar : SqBody body payload)
    (rest : List α) :
    quoteClose quote slash (body.map f ++ quote :: rest) = some (body.map f ++ [quote], rest) := by
  induction grammar with
  | nil =>
    unfold quoteClose
    simp
  | @cons code c tail payload head _ ih =>
    cases head with
    | plain _ lo hi notQuote notSlash =>
      have q : f c ≠ quote := fun same => notQuote (map.onlyQuote c lo hi same)
      have s : f c ≠ slash := fun same => notSlash (map.onlySlash c lo hi same)
      simp only [List.map_cons, List.cons_append]
      unfold quoteClose
      simp [q, s, ih]
    | quote =>
      simp only [List.cons_append, List.nil_append, List.map_cons, map.atQuote, map.atSlash]
      unfold quoteClose
      simp [map.distinct, ih]
    | slash =>
      simp only [List.cons_append, List.nil_append, List.map_cons, map.atSlash]
      unfold quoteClose
      simp [map.distinct, ih]

theorem quotedPrefix_atom {α : Type} [DecidableEq α] {f : Char → α} {quote slash : α}
    (map : QuoteMap f quote slash) {code payload : List Char} (grammar : QuotedAtom code payload)
    (rest : List α) : quotedPrefix quote slash (code.map f ++ rest) = some (code.map f, rest) := by
  cases grammar with
  | atom _ body =>
    have close := quoteClose_body map body rest
    simp only [List.map_cons, List.map_append, List.map_nil, List.cons_append, List.nil_append,
      List.append_assoc, map.atQuote]
    simp [quotedPrefix, close]

theorem charQuoteMap : QuoteMap id '\'' '\\' where
  atQuote := rfl
  atSlash := rfl
  onlyQuote := fun _ _ _ same => same
  onlySlash := fun _ _ _ same => same

theorem byteQuoteMap : QuoteMap asciiByte 39 92 where
  atQuote := rfl
  atSlash := rfl
  onlyQuote := fun c _ hi same => by
    have value := asciiByte_value c (by omega)
    rw [same] at value
    exact (char_eq_iff_nat c '\'').mpr (by simpa using value.symm)
  onlySlash := fun c _ hi same => by
    have value := asciiByte_value c (by omega)
    rw [same] at value
    exact (char_eq_iff_nat c '\\').mpr (by simpa using value.symm)

/-- Two quoted atoms at the start of the same characters are the same atom. -/
theorem quoted_prefix_chars {left right : List Char} {leftPayload rightPayload : List Char}
    {leftRest rightRest : List Char} (first : QuotedAtom left leftPayload)
    (second : QuotedAtom right rightPayload) (same : left ++ leftRest = right ++ rightRest) :
    left = right ∧ leftRest = rightRest := by
  have one := quotedPrefix_atom charQuoteMap first leftRest
  have two := quotedPrefix_atom charQuoteMap second rightRest
  simp only [List.map_id] at one two
  rw [same, two] at one
  simpa using one.symm

/-- Two quoted atoms at the start of the same bytes are the same atom. -/
theorem quoted_prefix_bytes {left right : String} {leftPayload rightPayload : List Char}
    {leftRest rightRest : Bytes} (first : QuotedAtom left.toList leftPayload)
    (second : QuotedAtom right.toList rightPayload)
    (same : spelling left ++ leftRest = spelling right ++ rightRest) :
    left = right ∧ leftRest = rightRest := by
  have one := quotedPrefix_atom byteQuoteMap first leftRest
  have two := quotedPrefix_atom byteQuoteMap second rightRest
  rw [← spelling_ascii left first.ascii] at one
  rw [← spelling_ascii right second.ascii] at two
  rw [same, two] at one
  have pair := Option.some.inj one
  exact ⟨spelling_injective (congrArg Prod.fst pair).symm, (congrArg Prod.snd pair).symm⟩

end Fang.TstpText
