/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent byte grammar for the quantified equality lexer. The proof reuses
   the accepted equality CNF ASCII/span lemmas; no decoder source is changed. -/
import EqualityQuantifiedInput
import EqualityLexing

namespace Fang.QuantifiedEqualityFrontend
open Frontend Source.Grammar EqualityFrontend

def QuantifiedEqualityPunctuation (character : Char) : Prop :=
  RawPunctuation character ∨ character = '=' ∨ character = '&' ∨ character = '!' ∨
    character = '?' ∨ character = '[' ∨ character = ']' ∨ character = ':'

/-- A single character cannot steal the start of a composite or rejected token. -/
def SingleAllowed (character : Char) (rest : List Char) : Prop :=
  (character = '=' → rest.head? ≠ some '>') ∧
  (character = '!' → rest.head? ≠ some '=') ∧
  (character = '~' → rest.head? ≠ some '&' ∧ rest.head? ≠ some '|')

inductive QuantifiedEqualityTokenization : List Char → Nat → List Frontend.Token → Prop where
  | empty (offset) : QuantifiedEqualityTokenization [] offset []
  | whitespace {character rest offset tokens} (space : RawSpace character)
      (tail : QuantifiedEqualityTokenization rest (offset + 1) tokens) :
      QuantifiedEqualityTokenization (character :: rest) offset tokens
  | lowerWord {character heads rest offset tokens} (first : SourceLower character)
      (maximal : MaximalPrefix SourceWord heads rest)
      (lowerTail : ∀ item ∈ heads, ¬ SourceUpper item)
      (tail : QuantifiedEqualityTokenization rest (offset + heads.length + 1) tokens) :
      QuantifiedEqualityTokenization (character :: (heads ++ rest)) offset
        ({text := String.ofList (character :: heads), offset} :: tokens)
  | upperWord {character heads rest offset tokens} (first : SourceUpper character)
      (maximal : MaximalPrefix SourceWord heads rest)
      (tail : QuantifiedEqualityTokenization rest (offset + heads.length + 1) tokens) :
      QuantifiedEqualityTokenization (character :: (heads ++ rest)) offset
        ({text := String.ofList (character :: heads), offset} :: tokens)
  | interpreted {heads rest offset tokens} (maximal : MaximalPrefix SourceWord heads rest)
      (spelled : String.ofList ('$' :: heads) = "$false" ∨ String.ofList ('$' :: heads) = "$true")
      (tail : QuantifiedEqualityTokenization rest (offset + heads.length + 1) tokens) :
      QuantifiedEqualityTokenization ('$' :: (heads ++ rest)) offset
        ({text := String.ofList ('$' :: heads), offset} :: tokens)
  | implication {rest offset tokens} (tail : QuantifiedEqualityTokenization rest (offset + 2) tokens) :
      QuantifiedEqualityTokenization ('=' :: '>' :: rest) offset ({text := "=>", offset} :: tokens)
  | disequality {rest offset tokens} (tail : QuantifiedEqualityTokenization rest (offset + 2) tokens) :
      QuantifiedEqualityTokenization ('!' :: '=' :: rest) offset ({text := "!=", offset} :: tokens)
  | punctuation {character rest offset tokens} (punctuation : QuantifiedEqualityPunctuation character)
      (allowed : SingleAllowed character rest)
      (tail : QuantifiedEqualityTokenization rest (offset + 1) tokens) :
      QuantifiedEqualityTokenization (character :: rest) offset
        ({text := String.singleton character, offset} :: tokens)

theorem quantifiedEqualityPunctuation_iff (character : Char) :
    ['(', ')', ',', '.', '|', '~', '=', '&', '!', '?', '[', ']', ':'].contains character = true ↔
      QuantifiedEqualityPunctuation character := by
  simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false,
    QuantifiedEqualityPunctuation, RawPunctuation, or_assoc]

theorem singleAllowed_iff (character : Char) (rest : List Char) :
    SingleAllowed character rest ↔
      ¬ (character == '=' && rest.head? == some '>') = true ∧
      ¬ (character == '!' && rest.head? == some '=') = true ∧
      ¬ (character == '~' && (rest.head? == some '&' || rest.head? == some '|')) = true := by
  simp only [SingleAllowed, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, not_and, not_or]

theorem punctuation_classes {character : Char} (punctuation : QuantifiedEqualityPunctuation character) :
    asciiSpace character = false ∧ (asciiLower character || asciiUpper character) = false ∧
      (character == '$') = false ∧ character.toNat < 128 := by
  rcases punctuation with ordinary | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  all_goals decide

theorem lexAux_sound (fuel : Nat) (input : List Char) (offset : Nat) (tokens : List Frontend.Token)
    (success : QuantifiedEqualityFrontend.lexAux fuel input offset = .ok tokens) :
    QuantifiedEqualityTokenization input offset tokens := by
  induction fuel generalizing input offset tokens with
  | zero => simp [QuantifiedEqualityFrontend.lexAux] at success
  | succ fuel ih =>
    cases input with
    | nil => cases success; exact .empty offset
    | cons character rest =>
      simp only [QuantifiedEqualityFrontend.lexAux] at success
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
              cases child : QuantifiedEqualityFrontend.lexAux fuel (rest.span sourceWordChar).2
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
                simpa only [← shape] using QuantifiedEqualityTokenization.lowerWord
                  ((sourceLower_iff _).mp lower) maximal noUpper (ih _ _ _ child)
          next notLower =>
            have upper : SourceUpper character := by
              have either : asciiLower character = true ∨ asciiUpper character = true := by
                simpa only [Bool.or_eq_true] using letter
              exact (sourceUpper_iff _).mp (either.resolve_left notLower)
            cases child : QuantifiedEqualityFrontend.lexAux fuel (rest.span sourceWordChar).2
                (offset + (rest.span sourceWordChar).1.length + 1) with
            | error error => rw [child] at success; cases success
            | ok tail =>
              rw [child] at success
              cases success
              obtain ⟨shape, maximal⟩ := source_span_spec rest
              simpa only [← shape] using QuantifiedEqualityTokenization.upperWord upper maximal (ih _ _ _ child)
        next notLetter =>
          split at success
          next dollar =>
            have same : character = '$' := by simpa using dollar
            subst character
            split at success
            next wrong => cases success
            next correct =>
              have spelled : String.ofList ('$' :: (rest.span sourceWordChar).1) = "$false" ∨
                  String.ofList ('$' :: (rest.span sourceWordChar).1) = "$true" := by
                by_cases falsity : String.ofList ('$' :: (rest.span sourceWordChar).1) = "$false"
                · exact .inl falsity
                · by_cases truth : String.ofList ('$' :: (rest.span sourceWordChar).1) = "$true"
                  · exact .inr truth
                  · exfalso
                    apply correct
                    simp only [Bool.and_eq_true, bne_iff_ne]
                    exact ⟨falsity, truth⟩
              cases child : QuantifiedEqualityFrontend.lexAux fuel (rest.span sourceWordChar).2
                  (offset + (rest.span sourceWordChar).1.length + 1) with
              | error error => rw [child] at success; cases success
              | ok tail =>
                rw [child] at success
                cases success
                obtain ⟨shape, maximal⟩ := source_span_spec rest
                simpa only [← shape] using QuantifiedEqualityTokenization.interpreted maximal spelled (ih _ _ _ child)
          next noDollar =>
            split at success
            next implication =>
              obtain ⟨rfl, head⟩ := (show character = '=' ∧ rest.head? = some '>' by simpa using implication)
              cases rest with
              | nil => cases head
              | cons first rest =>
                cases Option.some.inj head
                cases child : QuantifiedEqualityFrontend.lexAux fuel rest (offset + 2) with
                | error error => simp [child, bind, Except.bind] at success
                | ok tail =>
                  simp only [List.tail_cons, child, bind, Except.bind, pure, Except.pure] at success
                  cases success
                  exact .implication (ih _ _ _ child)
            next noImplication =>
              split at success
              next disequality =>
                obtain ⟨rfl, head⟩ := (show character = '!' ∧ rest.head? = some '=' by simpa using disequality)
                cases rest with
                | nil => cases head
                | cons first rest =>
                  cases Option.some.inj head
                  cases child : QuantifiedEqualityFrontend.lexAux fuel rest (offset + 2) with
                  | error error => simp [child, bind, Except.bind] at success
                  | ok tail =>
                    simp only [List.tail_cons, child, bind, Except.bind, pure, Except.pure] at success
                    cases success
                    exact .disequality (ih _ _ _ child)
              next noDisequality =>
                split at success
                next forbidden => cases success
                next noForbidden =>
                  split at success
                  next punctuation =>
                    cases child : QuantifiedEqualityFrontend.lexAux fuel rest (offset + 1) with
                    | error error => rw [child] at success; cases success
                    | ok tail =>
                      rw [child] at success
                      cases success
                      exact .punctuation ((quantifiedEqualityPunctuation_iff _).mp punctuation)
                        ((singleAllowed_iff _ _).mpr ⟨noImplication, noDisequality, noForbidden⟩) (ih _ _ _ child)
                  next noPunctuation => split at success <;> cases success

theorem lexAux_complete {input : List Char} {offset : Nat} {tokens : List Frontend.Token}
    (parsed : QuantifiedEqualityTokenization input offset tokens) (fuel : Nat)
    (enough : input.length < fuel) : QuantifiedEqualityFrontend.lexAux fuel input offset = .ok tokens := by
  induction parsed generalizing fuel with
  | empty offset => cases fuel with | zero => simp at enough | succ fuel => rfl
  | @whitespace character rest offset tokens space tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simpa only [QuantifiedEqualityFrontend.lexAux, (asciiSpace_raw _).mpr space, ite_true] using
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
      simp only [QuantifiedEqualityFrontend.lexAux, nonspace, lower, Bool.true_or, ↓reduceIte, span, noUpper]
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
      simp only [QuantifiedEqualityFrontend.lexAux, nonspace, lower, upper, Bool.false_or, ↓reduceIte, span]
      rw [next]
      rfl
  | @interpreted heads rest offset tokens maximal spelled tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have span := source_span_eq (input := heads ++ rest) rfl maximal
      have next := ih fuel (by simp only [List.length_cons, List.length_append] at enough; omega)
      rcases spelled with spelled | spelled
      all_goals
        simp [QuantifiedEqualityFrontend.lexAux, asciiSpace, asciiLower, asciiUpper, span, spelled, next]
        rfl
  | @implication rest offset tokens tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have next := ih fuel (by simp only [List.length_cons] at enough; omega)
      simp [QuantifiedEqualityFrontend.lexAux, asciiSpace, asciiLower, asciiUpper, next]
      rfl
  | @disequality rest offset tokens tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have next := ih fuel (by simp only [List.length_cons] at enough; omega)
      simp [QuantifiedEqualityFrontend.lexAux, asciiSpace, asciiLower, asciiUpper, next]
      rfl
  | @punctuation character rest offset tokens punctuation allowed tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨nonspace, nonletter, noDollar, _⟩ := punctuation_classes punctuation
      obtain ⟨noArrow, noDisequality, noForbidden⟩ := (singleAllowed_iff _ _).mp allowed
      have next := ih fuel (by simp only [List.length_cons] at enough; omega)
      simp only [QuantifiedEqualityFrontend.lexAux, nonspace, nonletter, noDollar, noArrow,
        noDisequality, noForbidden, (quantifiedEqualityPunctuation_iff _).mpr punctuation, ↓reduceIte]
      rw [next]
      rfl

theorem QuantifiedEqualityTokenization.unique {input offset left right}
    (first : QuantifiedEqualityTokenization input offset left) (second : QuantifiedEqualityTokenization input offset right) :
    left = right := by
  have leftRun := lexAux_complete first (input.length + 1) (by omega)
  have rightRun := lexAux_complete second (input.length + 1) (by omega)
  exact Except.ok.inj (leftRun.symm.trans rightRun)

theorem QuantifiedEqualityTokenization.ascii {input offset tokens}
    (parsed : QuantifiedEqualityTokenization input offset tokens) :
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
  | interpreted maximal spelled tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · decide
    · rcases List.mem_append.mp member with member | member
      · exact sourceWord_ascii (maximal.members character member)
      · exact ih character member
  | implication tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · decide
    · rcases List.mem_cons.mp member with rfl | member
      · decide
      · exact ih character member
  | disequality tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · decide
    · rcases List.mem_cons.mp member with rfl | member
      · decide
      · exact ih character member
  | punctuation punctuation allowed tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · exact (punctuation_classes punctuation).2.2.2
    · exact ih character member

theorem tokenize_iff (input : String) (tokens : List Frontend.Token) :
    QuantifiedEqualityFrontend.tokenize input = .ok tokens ↔ QuantifiedEqualityTokenization input.toList 0 tokens := by
  constructor
  · intro success
    unfold QuantifiedEqualityFrontend.tokenize at success
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
    simp only [QuantifiedEqualityFrontend.tokenize, ascii]
    exact lexAux_complete parsed _ (by omega)

def QuantifiedEqualityByteTokenization (bytes : List UInt8) (offset : Nat) (tokens : List Frontend.Token) : Prop :=
  ∃ characters, QuantifiedEqualityTokenization characters offset tokens ∧ characters.map asciiByte = bytes

theorem tokenize_bytes_iff (input : String) (tokens : List Frontend.Token) :
    QuantifiedEqualityFrontend.tokenize input = .ok tokens ↔
      QuantifiedEqualityByteTokenization (Source.Grammar.spelling input) 0 tokens := by
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

theorem QuantifiedEqualityByteTokenization.unique {bytes offset left right}
    (first : QuantifiedEqualityByteTokenization bytes offset left)
    (second : QuantifiedEqualityByteTokenization bytes offset right) : left = right := by
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

theorem QuantifiedEqualityTokenization.offsets {input offset tokens}
    (parsed : QuantifiedEqualityTokenization input offset tokens) :
    ∀ token ∈ tokens, offset ≤ token.offset ∧ token.offset < offset + input.length := by
  induction parsed with
  | empty => simp
  | whitespace space tail ih =>
    intro token member
    have bound := ih token member
    simp only [List.length_cons]
    omega
  | lowerWord first maximal lowerTail tail ih =>
    intro token member
    simp only [List.length_cons, List.length_append]
    rcases List.mem_cons.mp member with rfl | member
    · simp only; omega
    · have bound := ih token member; omega
  | upperWord first maximal tail ih =>
    intro token member
    simp only [List.length_cons, List.length_append]
    rcases List.mem_cons.mp member with rfl | member
    · simp only; omega
    · have bound := ih token member; omega
  | interpreted maximal spelled tail ih =>
    intro token member
    simp only [List.length_cons, List.length_append]
    rcases List.mem_cons.mp member with rfl | member
    · simp only; omega
    · have bound := ih token member; omega
  | implication tail ih =>
    intro token member
    simp only [List.length_cons]
    rcases List.mem_cons.mp member with rfl | member
    · simp only; omega
    · have bound := ih token member; omega
  | disequality tail ih =>
    intro token member
    simp only [List.length_cons]
    rcases List.mem_cons.mp member with rfl | member
    · simp only; omega
    · have bound := ih token member; omega
  | punctuation punctuation allowed tail ih =>
    intro token member
    simp only [List.length_cons]
    rcases List.mem_cons.mp member with rfl | member
    · simp only; omega
    · have bound := ih token member; omega

theorem tokenize_offsets (input : String) (tokens : List Frontend.Token)
    (success : QuantifiedEqualityFrontend.tokenize input = .ok tokens) :
    ∀ token ∈ tokens, token.offset < (Source.Grammar.spelling input).length := by
  have parsed := (tokenize_iff input tokens).mp success
  intro token member
  have bound := (parsed.offsets token member).2
  rw [spelling_ascii input parsed.ascii, List.length_map]
  simpa using bound

end Fang.QuantifiedEqualityFrontend
