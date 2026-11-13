/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Declarative maximal-word lexing for the equality CNF source dialect. -/
import EqualitySourceInput
import Fang.FrontendLexer

namespace Fang.EqualityFrontend
open Frontend Source.Grammar

def SourceLower (character : Char) : Prop := 97 ≤ character.toNat ∧ character.toNat ≤ 122
def SourceUpper (character : Char) : Prop := 65 ≤ character.toNat ∧ character.toNat ≤ 90
def SourceWord (character : Char) : Prop :=
  SourceLower character ∨ SourceUpper character ∨
    (48 ≤ character.toNat ∧ character.toNat ≤ 57) ∨ character.toNat = 95

def EqualityPunctuation (character : Char) : Prop :=
  RawPunctuation character ∨ character = '='

/- These constructors specify characters, maximal boundaries and exact offsets.
   They contain no result of lexAux, tokenize or the source parser. -/
inductive EqualityTokenization : List Char → Nat → List Frontend.Token → Prop where
  | empty (offset) : EqualityTokenization [] offset []
  | whitespace {character rest offset tokens} (space : RawSpace character)
      (tail : EqualityTokenization rest (offset + 1) tokens) :
      EqualityTokenization (character :: rest) offset tokens
  | lowerWord {character heads rest offset tokens} (first : SourceLower character)
      (maximal : MaximalPrefix SourceWord heads rest)
      (lowerTail : ∀ item ∈ heads, ¬ SourceUpper item)
      (tail : EqualityTokenization rest (offset + heads.length + 1) tokens) :
      EqualityTokenization (character :: (heads ++ rest)) offset
        ({text := String.ofList (character :: heads), offset} :: tokens)
  | upperWord {character heads rest offset tokens} (first : SourceUpper character)
      (maximal : MaximalPrefix SourceWord heads rest)
      (tail : EqualityTokenization rest (offset + heads.length + 1) tokens) :
      EqualityTokenization (character :: (heads ++ rest)) offset
        ({text := String.ofList (character :: heads), offset} :: tokens)
  | falsity {heads rest offset tokens} (maximal : MaximalPrefix SourceWord heads rest)
      (spelled : String.ofList ('$' :: heads) = "$false")
      (tail : EqualityTokenization rest (offset + heads.length + 1) tokens) :
      EqualityTokenization ('$' :: (heads ++ rest)) offset ({text := "$false", offset} :: tokens)
  | disequality {rest offset tokens} (tail : EqualityTokenization rest (offset + 2) tokens) :
      EqualityTokenization ('!' :: '=' :: rest) offset ({text := "!=", offset} :: tokens)
  | punctuation {character rest offset tokens} (punctuation : EqualityPunctuation character)
      (tail : EqualityTokenization rest (offset + 1) tokens) :
      EqualityTokenization (character :: rest) offset
        ({text := String.singleton character, offset} :: tokens)

theorem sourceLower_iff (character : Char) : asciiLower character = true ↔ SourceLower character := by
  exact asciiLower_nat character

theorem sourceUpper_iff (character : Char) : asciiUpper character = true ↔ SourceUpper character := by
  exact asciiUpper_nat character

theorem sourceWord_iff (character : Char) : sourceWordChar character = true ↔ SourceWord character := by
  simp only [sourceWordChar, Bool.or_eq_true, sourceLower_iff, sourceUpper_iff,
    asciiDigit_nat, beq_iff_eq, char_eq_iff_nat, SourceWord, or_assoc]
  rfl

theorem sourceWord_ascii {character : Char} (word : SourceWord character) : character.toNat < 128 := by
  simp only [SourceWord, SourceLower, SourceUpper] at word
  omega

theorem sourceWord_not_space {character : Char} (word : SourceWord character) :
    ¬ asciiSpace character = true := by
  intro space
  have raw := (asciiSpace_raw character).mp space
  have byte := asciiByte_value character raw.1
  simp only [RawSpace, IsSpace] at raw
  simp only [SourceWord, SourceLower, SourceUpper] at word
  omega

theorem source_span_spec (input : List Char) :
    input = (input.span sourceWordChar).1 ++ (input.span sourceWordChar).2 ∧
      MaximalPrefix SourceWord (input.span sourceWordChar).1 (input.span sourceWordChar).2 := by
  obtain ⟨shape, members, boundary⟩ := span_spec sourceWordChar input
  exact ⟨shape, ⟨fun item member => (sourceWord_iff item).mp (members item member),
    fun item tail equal word => boundary item tail equal ((sourceWord_iff item).mpr word)⟩⟩

theorem source_span_eq {input heads rest : List Char} (shape : input = heads ++ rest)
    (maximal : MaximalPrefix SourceWord heads rest) : input.span sourceWordChar = (heads, rest) := by
  obtain ⟨actualShape, actualMaximal⟩ := source_span_spec input
  obtain ⟨frontEqual, restEqual⟩ := actualMaximal.unique maximal (actualShape.symm.trans shape)
  exact Prod.ext frontEqual restEqual

theorem equalityPunctuation_iff (character : Char) :
    ['(', ')', ',', '.', '|', '~', '='].contains character = true ↔ EqualityPunctuation character := by
  simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false,
    EqualityPunctuation, RawPunctuation, or_assoc]

theorem lexAux_sound (fuel : Nat) (input : List Char) (offset : Nat) (tokens : List Frontend.Token)
    (success : EqualityFrontend.lexAux fuel input offset = .ok tokens) :
    EqualityTokenization input offset tokens := by
  induction fuel generalizing input offset tokens with
  | zero => simp [EqualityFrontend.lexAux] at success
  | succ fuel ih =>
    cases input with
    | nil => cases success; exact .empty offset
    | cons character rest =>
      simp only [EqualityFrontend.lexAux] at success
      split at success
      next space => exact .whitespace ((asciiSpace_raw _).mp space) (ih _ _ _ success)
      next nonspace =>
        split at success
        next letter =>
          split at success
          next lower =>
            cases uppercase : (rest.span sourceWordChar).1.findIdx? asciiUpper with
            | some index => simp [uppercase] at success
            | none =>
              simp only [uppercase] at success
              cases child : EqualityFrontend.lexAux fuel (rest.span sourceWordChar).2
                  (offset + (rest.span sourceWordChar).1.length + 1) with
              | error error => rw [child] at success; cases success
              | ok tail =>
                rw [child] at success
                cases success
                obtain ⟨shape, maximal⟩ := source_span_spec rest
                have noUpper : ∀ item ∈ (rest.span sourceWordChar).1, ¬ SourceUpper item := by
                  intro item member upper
                  have none := List.findIdx?_eq_none_iff.mp uppercase item member
                  have yes := (sourceUpper_iff item).mpr upper
                  simp [yes] at none
                simpa only [← shape] using EqualityTokenization.lowerWord
                  ((sourceLower_iff _).mp lower) maximal noUpper (ih _ _ _ child)
          next notLower =>
            have upper : SourceUpper character := by
              have either : asciiLower character = true ∨ asciiUpper character = true := by
                simpa only [Bool.or_eq_true] using letter
              exact (sourceUpper_iff _).mp (either.resolve_left notLower)
            cases child : EqualityFrontend.lexAux fuel (rest.span sourceWordChar).2
                (offset + (rest.span sourceWordChar).1.length + 1) with
            | error error => rw [child] at success; cases success
            | ok tail =>
              rw [child] at success
              cases success
              obtain ⟨shape, maximal⟩ := source_span_spec rest
              simpa only [← shape] using EqualityTokenization.upperWord upper maximal (ih _ _ _ child)
        next notLetter =>
          split at success
          next dollar =>
            have same : character = '$' := by simpa using dollar
            subst character
            split at success
            next wrong => cases success
            next correct =>
              have spelled : String.ofList ('$' :: (rest.span sourceWordChar).1) = "$false" := by
                simpa using correct
              cases child : EqualityFrontend.lexAux fuel (rest.span sourceWordChar).2
                  (offset + (rest.span sourceWordChar).1.length + 1) with
              | error error => rw [child] at success; cases success
              | ok tail =>
                rw [child] at success
                cases success
                obtain ⟨shape, maximal⟩ := source_span_spec rest
                simpa only [← shape] using EqualityTokenization.falsity maximal spelled (ih _ _ _ child)
          next noDollar =>
            split at success
            next disequality =>
              obtain ⟨rfl, head⟩ := (show character = '!' ∧ rest.head? = some '=' by simpa using disequality)
              cases rest with
              | nil => cases head
              | cons first rest =>
                cases Option.some.inj head
                cases child : EqualityFrontend.lexAux fuel rest (offset + 2) with
                | error error => simp [child, bind, Except.bind] at success
                | ok tail =>
                  simp only [List.tail_cons, child, bind, Except.bind, pure, Except.pure] at success
                  cases success
                  exact .disequality (ih _ _ _ child)
            next noDisequality =>
              split at success
              next punctuation =>
                cases child : EqualityFrontend.lexAux fuel rest (offset + 1) with
                | error error => rw [child] at success; cases success
                | ok tail =>
                  rw [child] at success
                  cases success
                  exact .punctuation ((equalityPunctuation_iff _).mp punctuation) (ih _ _ _ child)
              next noPunctuation => split at success <;> cases success

theorem lexAux_complete {input : List Char} {offset : Nat} {tokens : List Frontend.Token}
    (parsed : EqualityTokenization input offset tokens) (fuel : Nat)
    (enough : input.length < fuel) : EqualityFrontend.lexAux fuel input offset = .ok tokens := by
  induction parsed generalizing fuel with
  | empty offset => cases fuel with | zero => simp at enough | succ fuel => rfl
  | @whitespace character rest offset tokens space tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simpa only [EqualityFrontend.lexAux, (asciiSpace_raw _).mpr space, ite_true] using
        ih fuel (by simp only [List.length_cons] at enough; omega)
  | @lowerWord character heads rest offset tokens first maximal lowerTail tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have lower := (sourceLower_iff character).mpr first
      have nonspace := sourceWord_not_space (Or.inl first)
      have span := source_span_eq (input := heads ++ rest) rfl maximal
      have noUpper : heads.findIdx? asciiUpper = none := by
        apply List.findIdx?_eq_none_iff.mpr
        intro item member
        apply Bool.eq_false_iff.mpr
        exact fun upper => lowerTail item member ((sourceUpper_iff _).mp upper)
      have next := ih fuel (by simp only [List.length_cons, List.length_append] at enough; omega)
      simp only [EqualityFrontend.lexAux, nonspace, lower, Bool.true_or, ↓reduceIte, span, noUpper]
      rw [next]
      rfl
  | @upperWord character heads rest offset tokens first maximal tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have upper := (sourceUpper_iff character).mpr first
      have lower : asciiLower character = false := by
        apply Bool.eq_false_iff.mpr
        intro lower
        have low := (sourceLower_iff character).mp lower
        simp only [SourceUpper] at first
        simp only [SourceLower] at low
        omega
      have nonspace := sourceWord_not_space (Or.inr (Or.inl first))
      have span := source_span_eq (input := heads ++ rest) rfl maximal
      have next := ih fuel (by simp only [List.length_cons, List.length_append] at enough; omega)
      simp only [EqualityFrontend.lexAux, nonspace, lower, upper, Bool.false_or, ↓reduceIte, span]
      rw [next]
      rfl
  | @falsity heads rest offset tokens maximal spelled tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have span := source_span_eq (input := heads ++ rest) rfl maximal
      have next := ih fuel (by simp only [List.length_cons, List.length_append] at enough; omega)
      simp [EqualityFrontend.lexAux, asciiSpace, asciiLower, asciiUpper, span, spelled, next]
      rfl
  | @disequality rest offset tokens tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have next := ih fuel (by simp only [List.length_cons] at enough; omega)
      simp [EqualityFrontend.lexAux, asciiSpace, asciiLower, asciiUpper, next]
      rfl
  | @punctuation character rest offset tokens punctuation tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have nonspace : asciiSpace character = false := by
        rcases punctuation with ordinary | rfl
        · rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · decide
      have nonletter : (asciiLower character || asciiUpper character) = false := by
        rcases punctuation with ordinary | rfl
        · rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · decide
      have noDollar : (character == '$') = false := by
        rcases punctuation with ordinary | rfl
        · rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · decide
      have notBang : (character == '!') = false := by
        rcases punctuation with ordinary | rfl
        · rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        · decide
      have next := ih fuel (by simp only [List.length_cons] at enough; omega)
      simp only [EqualityFrontend.lexAux, nonspace, nonletter, noDollar, notBang,
        Bool.false_and, (equalityPunctuation_iff _).mpr punctuation, ↓reduceIte]
      rw [next]
      rfl

theorem EqualityTokenization.unique {input offset left right}
    (first : EqualityTokenization input offset left) (second : EqualityTokenization input offset right) :
    left = right := by
  have leftRun := lexAux_complete first (input.length + 1) (by omega)
  have rightRun := lexAux_complete second (input.length + 1) (by omega)
  exact Except.ok.inj (leftRun.symm.trans rightRun)

theorem EqualityTokenization.ascii {input offset tokens}
    (parsed : EqualityTokenization input offset tokens) :
    ∀ character ∈ input, character.toNat < 128 := by
  induction parsed with
  | empty => simp
  | whitespace space tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · exact space.1
    · exact ih character member
  | lowerWord first maximal lowerTail tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · exact sourceWord_ascii (.inl first)
    · rcases List.mem_append.mp member with member | member
      · exact sourceWord_ascii (maximal.members character member)
      · exact ih character member
  | upperWord first maximal tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · exact sourceWord_ascii (.inr (.inl first))
    · rcases List.mem_append.mp member with member | member
      · exact sourceWord_ascii (maximal.members character member)
      · exact ih character member
  | falsity maximal spelled tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · decide
    · rcases List.mem_append.mp member with member | member
      · exact sourceWord_ascii (maximal.members character member)
      · exact ih character member
  | disequality tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · decide
    · rcases List.mem_cons.mp member with rfl | member
      · decide
      · exact ih character member
  | punctuation punctuation tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · rcases punctuation with ordinary | rfl
      · exact rawPunctuation_ascii ordinary
      · decide
    · exact ih character member

theorem tokenize_iff (input : String) (tokens : List Frontend.Token) :
    EqualityFrontend.tokenize input = .ok tokens ↔ EqualityTokenization input.toList 0 tokens := by
  constructor
  · intro success
    unfold EqualityFrontend.tokenize at success
    dsimp only at success
    split at success
    · cases success
    · exact lexAux_sound _ _ _ _ success
  · intro parsed
    have ascii : input.toList.findIdx? (fun character => character.toNat > 127) = none := by
      apply List.findIdx?_eq_none_iff.mpr
      intro character member
      have bound := parsed.ascii character member
      simpa using (show ¬ 127 < character.toNat by omega)
    simp only [EqualityFrontend.tokenize, ascii]
    exact lexAux_complete parsed _ (by omega)

def EqualityByteTokenization (bytes : List UInt8) (offset : Nat) (tokens : List Frontend.Token) : Prop :=
  ∃ characters, EqualityTokenization characters offset tokens ∧ characters.map asciiByte = bytes

theorem tokenize_bytes_iff (input : String) (tokens : List Frontend.Token) :
    EqualityFrontend.tokenize input = .ok tokens ↔
      EqualityByteTokenization (Source.Grammar.spelling input) 0 tokens := by
  constructor
  · intro success
    have parsed := (tokenize_iff input tokens).mp success
    exact ⟨input.toList, parsed, (spelling_ascii input parsed.ascii).symm⟩
  · rintro ⟨characters, parsed, bytes⟩
    have same : String.ofList characters = input := by
      apply spelling_injective
      exact (spelling_ofList_ascii characters parsed.ascii).trans bytes
    apply (tokenize_iff input tokens).mpr
    simpa only [← same, String.toList_ofList] using parsed

end Fang.EqualityFrontend
