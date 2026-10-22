/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE.

The actual lexer against an independent maximal-word relation. Raw words are
not necessarily valid identifiers: word classification remains a parser task.
-/
import Fang.SourceAscii
import Init.Data.List.Find

namespace Fang.Frontend

open Source.Grammar

def RawWord (character : Char) : Prop :=
  character.toNat < 128 ∧ IsWord (asciiByte character)

def RawSpace (character : Char) : Prop :=
  character.toNat < 128 ∧ IsSpace (asciiByte character)

def RawPunctuation (character : Char) : Prop :=
  character = '(' ∨ character = ')' ∨ character = ',' ∨
  character = '.' ∨ character = '|' ∨ character = '~'

theorem wordChar_raw (character : Char) : wordChar character = true ↔ RawWord character := by
  constructor
  · intro word
    have ascii : character.toNat < 128 := by
      simp only [wordChar, Bool.or_eq_true, asciiLower_nat, asciiUpper_nat,
        asciiDigit_nat, beq_iff_eq, char_eq_iff_nat] at word
      have underscore : '_'.toNat = 95 := rfl
      have dollar : '$'.toNat = 36 := rfl
      have hyphen : '-'.toNat = 45 := rfl
      rw [underscore, dollar, hyphen] at word
      omega
    exact ⟨ascii, (wordChar_iff character ascii).mp word⟩
  · rintro ⟨ascii, word⟩
    exact (wordChar_iff character ascii).mpr word

theorem asciiSpace_raw (character : Char) : asciiSpace character = true ↔ RawSpace character := by
  constructor
  · intro space
    have ascii : character.toNat < 128 := by
      simp only [asciiSpace, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq, char_eq_iff_nat] at space
      have spaceValue : ' '.toNat = 32 := rfl
      rw [spaceValue] at space
      omega
    exact ⟨ascii, (asciiSpace_iff character ascii).mp space⟩
  · rintro ⟨ascii, space⟩
    exact (asciiSpace_iff character ascii).mpr space

theorem punctuation_raw (character : Char) :
    ['(', ')', ',', '.', '|', '~'].contains character = true ↔ RawPunctuation character := by
  simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false, RawPunctuation]

theorem rawWord_not_space {character : Char} (word : RawWord character) :
    ¬ RawSpace character := fun space => word_not_space word.2 space.2

theorem rawPunctuation_ascii {character : Char} (punctuation : RawPunctuation character) :
    character.toNat < 128 := by
  rcases punctuation with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rawPunctuation_not_word {character : Char} (punctuation : RawPunctuation character) :
    ¬ RawWord character := by
  rw [← wordChar_raw]
  rcases punctuation with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rawPunctuation_not_space {character : Char} (punctuation : RawPunctuation character) :
    ¬ RawSpace character := by
  rw [← asciiSpace_raw]
  rcases punctuation with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

inductive RawTokenization : List Char → Nat → List Token → Prop where
  | empty (offset) : RawTokenization [] offset []
  | whitespace {character rest offset tokens} (space : RawSpace character)
      (tail : RawTokenization rest (offset + 1) tokens) :
      RawTokenization (character :: rest) offset tokens
  | word {front rest offset tokens} (nonempty : front ≠ [])
      (maximal : MaximalPrefix RawWord front rest)
      (tail : RawTokenization rest (offset + front.length) tokens) :
      RawTokenization (front ++ rest) offset ({ text := String.ofList front, offset } :: tokens)
  | punctuation {character rest offset tokens} (punctuation : RawPunctuation character)
      (tail : RawTokenization rest (offset + 1) tokens) :
      RawTokenization (character :: rest) offset
        ({ text := String.singleton character, offset } :: tokens)

theorem span_loop_spec (predicate : α → Bool) (input accumulated : List α)
    (accepted : ∀ item ∈ accumulated, predicate item = true) :
    let result := List.span.loop predicate input accumulated
    accumulated.reverse ++ input = result.1 ++ result.2 ∧
      MaximalPrefix (fun item => predicate item = true) result.1 result.2 := by
  induction input generalizing accumulated with
  | nil =>
    simp only [List.span.loop]
    refine ⟨by simp, ⟨?_, ?_⟩⟩
    · intro item member
      exact accepted item (List.mem_reverse.mp member)
    · intro item tail impossible
      cases impossible
  | cons head rest ih =>
    cases chosen : predicate head with
    | false =>
      simp only [List.span.loop, chosen]
      refine ⟨trivial, ⟨?_, ?_⟩⟩
      · intro item member
        exact accepted item (List.mem_reverse.mp member)
      · intro item tail equal
        cases equal
        simp [chosen]
    | true =>
      simp only [List.span.loop, chosen]
      have next := ih (head :: accumulated) (by
        intro item member
        rcases List.mem_cons.mp member with rfl | member
        · exact chosen
        · exact accepted item member)
      simpa [List.reverse_cons, List.append_assoc] using next

theorem span_spec (predicate : α → Bool) (input : List α) :
    input = (input.span predicate).1 ++ (input.span predicate).2 ∧
      MaximalPrefix (fun item => predicate item = true)
        (input.span predicate).1 (input.span predicate).2 := by
  simpa [List.span] using span_loop_spec predicate input [] (by simp)

theorem word_span_spec (input : List Char) :
    input = (input.span wordChar).1 ++ (input.span wordChar).2 ∧
      MaximalPrefix RawWord (input.span wordChar).1 (input.span wordChar).2 := by
  obtain ⟨shape, members, boundary⟩ := span_spec wordChar input
  exact ⟨shape, ⟨fun item member => (wordChar_raw item).mp (members item member),
    fun item tail equal word => boundary item tail equal ((wordChar_raw item).mpr word)⟩⟩

theorem span_eq_of_maximal (input front rest : List Char)
    (shape : input = front ++ rest) (maximal : MaximalPrefix RawWord front rest) :
    input.span wordChar = (front, rest) := by
  obtain ⟨actualShape, actualMaximal⟩ := word_span_spec input
  obtain ⟨frontEqual, restEqual⟩ := actualMaximal.unique maximal (actualShape.symm.trans shape)
  exact Prod.ext frontEqual restEqual

theorem lexAux_sound (fuel : Nat) (input : List Char) (offset : Nat) (tokens : List Token)
    (success : lexAux fuel input offset = .ok tokens) : RawTokenization input offset tokens := by
  induction fuel generalizing input offset tokens with
  | zero => simp [lexAux] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp only [lexAux, Except.ok.injEq] at success
      subst tokens
      exact .empty offset
    | cons character rest =>
      simp only [lexAux] at success
      split at success
      next space =>
        exact .whitespace ((asciiSpace_raw character).mp space) (ih rest _ tokens success)
      next nonspace =>
        split at success
        next word =>
          cases child : lexAux fuel (rest.span wordChar).2
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
            have parsed := RawTokenization.word (by simp) maximal (ih _ _ tail child)
            simpa only [List.cons_append, ← shape] using parsed
        next nonword =>
          split at success
          next punctuation =>
            cases child : lexAux fuel rest (offset + 1) with
            | error error => rw [child] at success; cases success
            | ok tail =>
              rw [child] at success
              change Except.ok ({ text := String.singleton character, offset } :: tail) = Except.ok tokens at success
              cases success
              exact .punctuation ((punctuation_raw character).mp punctuation) (ih _ _ tail child)
          next nonpunctuation =>
            split at success <;> cases success

theorem lexAux_complete {input : List Char} {offset : Nat} {tokens : List Token}
    (parsed : RawTokenization input offset tokens) (fuel : Nat)
    (enough : input.length < fuel) : lexAux fuel input offset = .ok tokens := by
  induction parsed generalizing fuel with
  | empty offset =>
    cases fuel with
    | zero => simp at enough
    | succ fuel => rfl
  | @whitespace character rest offset tokens space tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have isSpace := (asciiSpace_raw character).mpr space
      simpa only [lexAux, isSpace, ite_true] using ih fuel (by simp only [List.length_cons] at enough; omega)
  | @word front rest offset tokens nonempty maximal tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases front with
      | nil => exact False.elim (nonempty rfl)
      | cons character heads =>
        have word := maximal.members character List.mem_cons_self
        have isWord := (wordChar_raw character).mpr word
        have nonspace : ¬ asciiSpace character = true := by
          intro space
          exact rawWord_not_space word ((asciiSpace_raw character).mp space)
        have tailMaximal : MaximalPrefix RawWord heads rest :=
          ⟨fun item member => maximal.members item (List.mem_cons_of_mem _ member), maximal.boundary⟩
        have span := span_eq_of_maximal (heads ++ rest) heads rest rfl tailMaximal
        have next := ih fuel (by simp only [List.length_append, List.length_cons] at enough; omega)
        simp only [List.cons_append, lexAux, nonspace, isWord, ite_true, span]
        rw [next]
        rfl
  | @punctuation character rest offset tokens punctuation tail ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have nonspace : ¬ asciiSpace character = true := by
        intro space
        exact rawPunctuation_not_space punctuation ((asciiSpace_raw character).mp space)
      have nonword : ¬ wordChar character = true := by
        intro word
        exact rawPunctuation_not_word punctuation ((wordChar_raw character).mp word)
      have isPunctuation := (punctuation_raw character).mpr punctuation
      have next := ih fuel (by simp only [List.length_cons] at enough; omega)
      simp only [lexAux, nonspace, nonword, isPunctuation, ite_true]
      rw [next]
      rfl

theorem RawTokenization.ascii {input : List Char} {offset : Nat} {tokens : List Token}
    (parsed : RawTokenization input offset tokens) :
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
  | punctuation punctuation tail ih =>
    intro character member
    rcases List.mem_cons.mp member with rfl | member
    · exact rawPunctuation_ascii punctuation
    · exact ih character member

theorem tokenize_sound (input : String) (tokens : List Token)
    (success : tokenize input = .ok tokens) : RawTokenization input.toList 0 tokens := by
  unfold tokenize at success
  dsimp only at success
  split at success
  next offset found => cases success
  next valid => exact lexAux_sound _ _ _ _ success

theorem tokenize_complete (input : String) (tokens : List Token)
    (parsed : RawTokenization input.toList 0 tokens) : tokenize input = .ok tokens := by
  have ascii : input.toList.findIdx? (fun c => c.toNat > 127) = none := by
    apply List.findIdx?_eq_none_iff.mpr
    intro character member
    have bound := parsed.ascii character member
    simp only [decide_eq_false_iff_not]
    omega
  simp only [tokenize, ascii]
  exact lexAux_complete parsed _ (by omega)

theorem tokenize_iff (input : String) (tokens : List Token) :
    tokenize input = .ok tokens ↔ RawTokenization input.toList 0 tokens :=
  ⟨tokenize_sound input tokens, tokenize_complete input tokens⟩

def RawTokenSpelling (raw : Token) (token : Source.Grammar.Token) : Prop :=
  WordSpelling (spelling raw.text) token ∨
    ∃ byte, Punctuation byte token ∧ spelling raw.text = [byte]

inductive ClassifiedTokens : List Token → List Source.Grammar.Token → Prop where
  | nil : ClassifiedTokens [] []
  | cons {raw token raws tokens} (head : RawTokenSpelling raw token)
      (tail : ClassifiedTokens raws tokens) : ClassifiedTokens (raw :: raws) (token :: tokens)

theorem rawPunctuation_spelled {character : Char} (punctuation : RawPunctuation character) :
    ∃ token, Punctuation (asciiByte character) token := by
  rcases punctuation with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.lparen, .lparen⟩
  · exact ⟨.rparen, .rparen⟩
  · exact ⟨.comma, .comma⟩
  · exact ⟨.period, .period⟩
  · exact ⟨.disjoin, .disjoin⟩
  · exact ⟨.negate, .negate⟩

theorem maximal_map_bytes {front rest : List Char}
    (maximal : MaximalPrefix RawWord front rest)
    (ascii : ∀ character ∈ rest, character.toNat < 128) :
    MaximalPrefix IsWord (front.map asciiByte) (rest.map asciiByte) := by
  constructor
  · intro byte member
    obtain ⟨character, present, rfl⟩ := List.mem_map.mp member
    exact (maximal.members character present).2
  · intro byte tail shape word
    cases rest with
    | nil => cases shape
    | cons character characters =>
      have equal := (List.cons.inj shape).1
      subst byte
      exact maximal.boundary character characters rfl
        ⟨ascii character List.mem_cons_self, word⟩

theorem RawTokenization.toGrammar {input : List Char} {offset : Nat} {raw : List Token}
    (parsed : RawTokenization input offset raw)
    {tokens : List Source.Grammar.Token}
    (classified : ClassifiedTokens raw tokens) :
    Source.Grammar.Tokenization (input.map asciiByte) tokens := by
  induction parsed generalizing tokens with
  | empty =>
    cases classified
    exact .empty
  | whitespace space tail ih =>
    exact .whitespace space.2 (ih classified)
  | @word front rest offset raw nonempty maximal tail ih =>
    cases classified with
    | cons headClass tailClass =>
      have frontAscii : ∀ character ∈ front, character.toNat < 128 := by
        intro character member
        exact (maximal.members character member).1
      have bytes := spelling_ofList_ascii front frontAscii
      simp only [RawTokenSpelling] at headClass
      rcases headClass with word | ⟨byte, punctuation, singleton⟩
      · rw [bytes] at word
        exact .token (.word (by simp) (maximal_map_bytes maximal tail.ascii) word) (ih tailClass)
      · rw [bytes] at singleton
        cases front with
        | nil => exact False.elim (nonempty rfl)
        | cons character characters =>
          have same := (List.cons.inj singleton).1
          exact False.elim (punctuation.not_word (same ▸ (maximal.members character List.mem_cons_self).2))
  | @punctuation character rest offset raw punctuation tail ih =>
    cases classified with
    | cons headClass tailClass =>
      have bytes : spelling (String.singleton character) = [asciiByte character] := by
        exact spelling_ofList_ascii [character] (by
          intro item member
          have same : item = character := by simpa using member
          subst item
          exact rawPunctuation_ascii punctuation)
      simp only [RawTokenSpelling] at headClass
      rcases headClass with word | ⟨byte, spelled, singleton⟩
      · rw [bytes] at word
        obtain ⟨token, actual⟩ := rawPunctuation_spelled punctuation
        exact False.elim (actual.not_word (word.word_bytes.2 _ List.mem_cons_self))
      · rw [bytes] at singleton
        have same := (List.cons.inj singleton).1
        subst byte
        exact .token (.punctuation spelled) (ih tailClass)

theorem tokenize_toGrammar (input : String) (raw : List Token)
    (success : tokenize input = .ok raw) (tokens : List Source.Grammar.Token)
    (classified : ClassifiedTokens raw tokens) :
    Source.Grammar.Tokenization (spelling input) tokens := by
  have parsed := tokenize_sound input raw success
  rw [spelling_ascii input parsed.ascii]
  exact parsed.toGrammar classified

theorem RawTokenization.offsets {input : List Char} {offset : Nat} {tokens : List Token}
    (parsed : RawTokenization input offset tokens) :
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
  | punctuation punctuation tail ih =>
    intro token member
    simp only [List.length_cons]
    rcases List.mem_cons.mp member with rfl | member
    · simp only
      omega
    · have bound := ih token member
      omega

theorem tokenize_offsets (input : String) (tokens : List Token)
    (success : tokenize input = .ok tokens) :
    ∀ token ∈ tokens, token.offset < (spelling input).length := by
  have parsed := tokenize_sound input tokens success
  intro token member
  have bound := (parsed.offsets token member).2
  rw [spelling_ascii input parsed.ascii, List.length_map]
  simpa using bound

end Fang.Frontend

#print axioms Fang.Frontend.lexAux_sound
#print axioms Fang.Frontend.lexAux_complete
#print axioms Fang.Frontend.tokenize_iff
#print axioms Fang.Frontend.tokenize_toGrammar
#print axioms Fang.Frontend.tokenize_offsets
