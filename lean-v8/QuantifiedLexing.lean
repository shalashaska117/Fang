/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE.
   Adapted from the accepted universal-prefix lexer proof, adding existential punctuation.
   This is an independent checker proof candidate, not generated Rust. -/
import QuantifiedInput
import Fang.FrontendClassification

namespace Fang.QuantifiedFrontend
open Frontend Source.Grammar

def QuantifiedPunctuation (character : Char) : Prop :=
  Frontend.RawPunctuation character ∨ character = '&' ∨ character = '!' ∨ character = '?' ∨
    character = '[' ∨ character = ']' ∨ character = ':'

def NoNandNor (character : Char) (rest : List Char) : Prop :=
  character = '~' → rest.head? ≠ some '&' ∧ rest.head? ≠ some '|'

/- The word and whitespace classes are byte-defined by Source.Grammar.
   Implication is one token; an adjacent ~& or ~| is outside this grammar. -/
inductive QuantifiedTokenization : List Char → Nat → List Frontend.Token → Prop where
  | empty (offset) : QuantifiedTokenization [] offset []
  | whitespace {character rest offset tokens} (space : RawSpace character)
      (tail : QuantifiedTokenization rest (offset + 1) tokens) :
      QuantifiedTokenization (character :: rest) offset tokens
  | word {front rest offset tokens} (nonempty : front ≠ [])
      (maximal : MaximalPrefix RawWord front rest)
      (tail : QuantifiedTokenization rest (offset + front.length) tokens) :
      QuantifiedTokenization (front ++ rest) offset ({ text := String.ofList front, offset } :: tokens)
  | implication {rest offset tokens} (tail : QuantifiedTokenization rest (offset + 2) tokens) :
      QuantifiedTokenization ('=' :: '>' :: rest) offset ({ text := "=>", offset } :: tokens)
  | punctuation {character rest offset tokens} (punctuation : QuantifiedPunctuation character)
      (allowed : NoNandNor character rest)
      (tail : QuantifiedTokenization rest (offset + 1) tokens) :
      QuantifiedTokenization (character :: rest) offset
        ({ text := String.singleton character, offset } :: tokens)

theorem quantifiedPunctuation_iff (character : Char) :
    ['(', ')', ',', '.', '|', '~', '&', '!', '?', '[', ']', ':'].contains character = true ↔ QuantifiedPunctuation character := by
  simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false,
    QuantifiedPunctuation, RawPunctuation, or_assoc]

theorem noNandNor_iff (character : Char) (rest : List Char) :
    ¬ (character == '~' && (rest.head? == some '&' || rest.head? == some '|')) = true ↔
      NoNandNor character rest := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, not_and, not_or, NoNandNor]

theorem quantifiedPunctuation_ascii {character : Char} (punctuation : QuantifiedPunctuation character) :
    character.toNat < 128 := by
  rcases punctuation with ordinary | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rawPunctuation_ascii ordinary
  all_goals decide

theorem quantifiedPunctuation_not_word {character : Char} (punctuation : QuantifiedPunctuation character) :
    ¬ wordChar character = true := by
  rcases punctuation with ordinary | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun word => rawPunctuation_not_word ordinary ((wordChar_raw _).mp word)
  all_goals decide

theorem quantifiedPunctuation_not_space {character : Char} (punctuation : QuantifiedPunctuation character) :
    ¬ asciiSpace character = true := by
  rcases punctuation with ordinary | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun space => rawPunctuation_not_space ordinary ((asciiSpace_raw _).mp space)
  all_goals decide

theorem quantifiedPunctuation_not_equal {character : Char} (punctuation : QuantifiedPunctuation character) :
    character ≠ '=' := by
  rcases punctuation with ordinary | rfl | rfl | rfl | rfl | rfl | rfl
  · rcases ordinary with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  all_goals decide

theorem quantified_lexAux_sound (fuel : Nat) (input : List Char) (offset : Nat) (tokens : List Frontend.Token)
    (success : QuantifiedFrontend.lexAux fuel input offset = .ok tokens) :
    QuantifiedTokenization input offset tokens := by
  induction fuel generalizing input offset tokens with
  | zero => simp [QuantifiedFrontend.lexAux] at success
  | succ fuel ih =>
    cases input with
    | nil => cases success; exact .empty offset
    | cons character rest =>
      simp only [QuantifiedFrontend.lexAux] at success
      split at success
      next space => exact .whitespace ((asciiSpace_raw _).mp space) (ih _ _ _ success)
      next nonspace =>
        split at success
        next word =>
          cases child : QuantifiedFrontend.lexAux fuel (rest.span wordChar).2
              (offset + (character :: (rest.span wordChar).1).length) with
          | error error => rw [child] at success; cases success
          | ok tail =>
            rw [child] at success
            change Except.ok ({ text := String.ofList (character :: (rest.span wordChar).1), offset } :: tail) = Except.ok tokens at success
            cases success
            obtain ⟨shape, members, boundary⟩ := word_span_spec rest
            have maximal : MaximalPrefix RawWord (character :: (rest.span wordChar).1)
                (rest.span wordChar).2 := by
              refine ⟨?_, boundary⟩
              intro item member
              rcases List.mem_cons.mp member with rfl | member
              · exact (wordChar_raw _).mp word
              · exact members item member
            have parsed := QuantifiedTokenization.word (by simp) maximal (ih _ _ tail child)
            simpa only [List.cons_append, ← shape] using parsed
        next nonword =>
          split at success
          next arrow =>
            obtain ⟨rfl, head⟩ := (show character = '=' ∧ rest.head? = some '>' by simpa using arrow)
            cases rest with
            | nil => cases head
            | cons first rest =>
              cases Option.some.inj head
              cases child : QuantifiedFrontend.lexAux fuel rest (offset + 2) with
              | error error => simp [child, bind, Except.bind] at success
              | ok tail =>
                simp only [List.tail_cons, child, bind, Except.bind, pure, Except.pure] at success
                cases success
                exact .implication (ih _ _ _ child)
          next noArrow =>
            split at success
            next forbidden => cases success
            next allowed =>
              split at success
              next punctuation =>
                cases child : QuantifiedFrontend.lexAux fuel rest (offset + 1) with
                | error error => rw [child] at success; cases success
                | ok tail =>
                  rw [child] at success
                  change Except.ok ({ text := String.singleton character, offset } :: tail) = Except.ok tokens at success
                  cases success
                  exact .punctuation ((quantifiedPunctuation_iff _).mp punctuation)
                    ((noNandNor_iff _ _).mp allowed) (ih _ _ _ child)
              next notPunctuation => split at success <;> cases success

theorem quantified_lexAux_complete {input : List Char} {offset : Nat} {tokens : List Frontend.Token}
    (parsed : QuantifiedTokenization input offset tokens) (fuel : Nat)
    (enough : input.length < fuel) : QuantifiedFrontend.lexAux fuel input offset = .ok tokens := by
  induction parsed generalizing fuel with
  | empty offset => cases fuel with | zero => simp at enough | succ fuel => rfl
  | @whitespace character rest offset tokens space tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simpa only [QuantifiedFrontend.lexAux, (asciiSpace_raw _).mpr space, ite_true] using
        ih fuel (by simp only [List.length_cons] at enough; omega)
  | @word front rest offset tokens nonempty maximal tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases front with
      | nil => exact False.elim (nonempty rfl)
      | cons character heads =>
        have word := maximal.members character List.mem_cons_self
        have isWord := (wordChar_raw _).mpr word
        have nonspace : ¬ asciiSpace character = true :=
          fun space => rawWord_not_space word ((asciiSpace_raw _).mp space)
        have tailMaximal : MaximalPrefix RawWord heads rest :=
          ⟨fun item member => maximal.members item (List.mem_cons_of_mem _ member), maximal.boundary⟩
        have span := span_eq_of_maximal (heads ++ rest) heads rest rfl tailMaximal
        have next := ih fuel (by simp only [List.length_append, List.length_cons] at enough; omega)
        simp only [List.cons_append, QuantifiedFrontend.lexAux, nonspace, isWord, ite_true, span]
        rw [next]
        rfl
  | @implication rest offset tokens tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have next := ih fuel (by simp only [List.length_cons] at enough; omega)
      simp [QuantifiedFrontend.lexAux, asciiSpace, wordChar, asciiLower, asciiUpper, asciiDigit, next]
      rfl
  | @punctuation character rest offset tokens punctuation allowed tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have nonspace := quantifiedPunctuation_not_space punctuation
      have nonword := quantifiedPunctuation_not_word punctuation
      have notEqual := quantifiedPunctuation_not_equal punctuation
      have notArrow : ¬ (character == '=' && rest.head? == some '>') = true := by
        simp only [Bool.and_eq_true, beq_iff_eq]
        exact fun h => notEqual h.1
      have notForbidden := (noNandNor_iff _ _).mpr allowed
      have isPunctuation := (quantifiedPunctuation_iff _).mpr punctuation
      have next := ih fuel (by simp only [List.length_cons] at enough; omega)
      simp only [QuantifiedFrontend.lexAux, nonspace, nonword, notArrow, notForbidden, isPunctuation,
        ite_true]
      rw [next]
      rfl

theorem QuantifiedTokenization.ascii {input offset tokens} (parsed : QuantifiedTokenization input offset tokens) :
    ∀ character ∈ input, character.toNat < 128 := by
  induction parsed with
  | empty => simp
  | whitespace space tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · exact space.1
    · exact ih character member
  | word nonempty maximal tail ih =>
    intro character member
    rcases List.mem_append.mp member with member | member
    · exact (maximal.members character member).1
    · exact ih character member
  | implication tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · decide
    · rcases List.mem_cons.mp member with rfl | member
      · decide
      · exact ih character member
  | punctuation punctuation allowed tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · exact quantifiedPunctuation_ascii punctuation
    · exact ih character member

theorem quantified_tokenize_iff (input : String) (tokens : List Frontend.Token) :
    QuantifiedFrontend.tokenize input = .ok tokens ↔ QuantifiedTokenization input.toList 0 tokens := by
  constructor
  · intro success
    unfold QuantifiedFrontend.tokenize at success
    split at success
    · cases success
    · exact quantified_lexAux_sound _ _ _ _ success
  · intro parsed
    have ascii : input.toList.any (fun c => c.toNat > 127) = false := by
      apply List.any_eq_false.mpr
      intro character member
      have bound := parsed.ascii character member
      simpa using (show ¬ 127 < character.toNat by omega)
    simp only [QuantifiedFrontend.tokenize, ascii, Bool.false_eq_true, ite_false]
    exact quantified_lexAux_complete parsed _ (by omega)

/- This byte relation is the ASCII transport of the declarative character
   grammar. Its witness contains no executable lexer or parser result. -/
def QuantifiedByteTokenization (bytes : List UInt8) (offset : Nat) (tokens : List Frontend.Token) : Prop :=
  ∃ characters, QuantifiedTokenization characters offset tokens ∧ characters.map asciiByte = bytes

theorem quantified_tokenize_bytes_iff (input : String) (tokens : List Frontend.Token) :
    QuantifiedFrontend.tokenize input = .ok tokens ↔
      QuantifiedByteTokenization (Source.Grammar.spelling input) 0 tokens := by
  constructor
  · intro success
    have parsed := (quantified_tokenize_iff input tokens).mp success
    exact ⟨input.toList, parsed, (spelling_ascii input parsed.ascii).symm⟩
  · rintro ⟨characters, parsed, bytes⟩
    have same : String.ofList characters = input := by
      apply spelling_injective
      exact (spelling_ofList_ascii characters parsed.ascii).trans bytes
    apply (quantified_tokenize_iff input tokens).mpr
    simpa only [← same, String.toList_ofList] using parsed

theorem QuantifiedTokenization.token_ascii {input offset tokens}
    (parsed : QuantifiedTokenization input offset tokens) :
    ∀ token ∈ tokens, ∀ character ∈ token.text.toList, character.toNat < 128 := by
  induction parsed with
  | empty => simp
  | whitespace space tail ih => exact ih
  | @word front rest offset tokens nonempty maximal tail ih =>
    intro token member character present
    rcases List.mem_cons.mp member with rfl | member
    · have member : character ∈ front := by simpa using present
      exact (maximal.members character member).1
    · exact ih token member character present
  | implication tail ih =>
    intro token member character present
    rcases List.mem_cons.mp member with rfl | member
    · have alternatives : character = '=' ∨ character = '>' := by simpa using present
      rcases alternatives with rfl | rfl <;> decide
    · exact ih token member character present
  | @punctuation first rest offset tokens punctuation allowed tail ih =>
    intro token member character present
    rcases List.mem_cons.mp member with rfl | member
    · have same : character = first := by simpa using present
      subst character
      exact quantifiedPunctuation_ascii punctuation
    · exact ih token member character present

theorem QuantifiedTokenization.offsets {input offset tokens}
    (parsed : QuantifiedTokenization input offset tokens) :
    ∀ token ∈ tokens, offset ≤ token.offset ∧ token.offset < offset + input.length := by
  induction parsed with
  | empty => simp
  | whitespace space tail ih =>
    intro token member
    have bound := ih token member
    simp only [List.length_cons]
    omega
  | @word front rest offset tokens nonempty maximal tail ih =>
    intro token member
    simp only [List.length_append]
    rcases List.mem_cons.mp member with rfl | member
    · have positive : 0 < front.length := List.length_pos_iff.mpr nonempty
      simp only
      omega
    · have bound := ih token member
      omega
  | implication tail ih =>
    intro token member
    simp only [List.length_cons]
    rcases List.mem_cons.mp member with rfl | member
    · simp only
      omega
    · have bound := ih token member
      omega
  | punctuation punctuation allowed tail ih =>
    intro token member
    simp only [List.length_cons]
    rcases List.mem_cons.mp member with rfl | member
    · simp only
      omega
    · have bound := ih token member
      omega

theorem quantified_tokenize_offsets (input : String) (tokens : List Frontend.Token)
    (success : QuantifiedFrontend.tokenize input = .ok tokens) :
    ∀ token ∈ tokens, token.offset < (Source.Grammar.spelling input).length := by
  have parsed := (quantified_tokenize_iff input tokens).mp success
  intro token member
  have bound := (parsed.offsets token member).2
  rw [spelling_ascii input parsed.ascii, List.length_map]
  simpa using bound

end Fang.QuantifiedFrontend
