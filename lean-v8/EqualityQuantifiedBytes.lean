/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Original-byte syntax and model transport for actual independent decoding.
   The numeric refutation premise remains separate from this source boundary. -/
import EqualityQuantifiedLexing
import EqualityQuantifiedUniqueness
import EqualityQuantifiedMeaning
import EqualityQuantifiedDeclaration

namespace Fang.NamedQuantifiedEquality.Grammar

/-- The source relation uses independent lexical and consuming syntax rules.
    Names must be distinct; no actual decoder execution occurs in this definition. -/
def Parses (bytes : List UInt8) (named : List Declaration) : Prop :=
  ∃ tokens, QuantifiedEqualityFrontend.QuantifiedEqualityByteTokenization bytes 0 tokens ∧
    ParsesTokens (tokens.map Frontend.Token.text) named

def BytesSatisfiable (bytes : List UInt8) : Prop :=
  ∃ named, Parses bytes named ∧ NamedQuantifiedEquality.Satisfiable named

theorem Parses.unique {bytes left right} (first : Parses bytes left) (second : Parses bytes right) :
    left = right := by
  obtain ⟨firstTokens, firstLexed, first⟩ := first
  obtain ⟨secondTokens, secondLexed, second⟩ := second
  have same := firstLexed.unique secondLexed
  cases same
  exact first.unique second

end Fang.NamedQuantifiedEquality.Grammar

namespace Fang.QuantifiedEqualityFrontend

def decode (input : String) : Except String Encoding.Encoded := do
  Encoding.encode (← decodeNamed input)

theorem Encoding.encode_names_unique {named : List NamedQuantifiedEquality.Declaration} {encoded}
    (success : Encoding.encode named = .ok encoded) :
    (named.map NamedQuantifiedEquality.Declaration.name).Nodup := by
  unfold Encoding.encode at success
  dsimp only at success
  split at success
  · cases success
  · rename_i unique
    simpa using unique

theorem decode_byte_encoding {input encoded} (success : decode input = .ok encoded) :
    ∃ named, decodeNamed input = .ok named ∧
      NamedQuantifiedEquality.Grammar.Parses (Source.Grammar.spelling input) named ∧
      Encoding.encode named = .ok encoded := by
  unfold decode at success
  cases namedRun : decodeNamed input with
  | error error => simp [namedRun, bind, Except.bind] at success
  | ok named =>
    have encodedRun : Encoding.encode named = .ok encoded := by
      simpa only [namedRun, bind, Except.bind] using success
    obtain ⟨tokens, tokenRun, parsed⟩ := decode_named_token_grammar namedRun
    exact ⟨named, rfl,
      ⟨tokens, (tokenize_bytes_iff input tokens).mp tokenRun, parsed,
        Encoding.encode_names_unique encodedRun⟩, encodedRun⟩

theorem decode_semantic_encoding {input encoded} (success : decode input = .ok encoded) :
    ∃ named signature symbols,
      NamedQuantifiedEquality.Grammar.Parses (Source.Grammar.spelling input) named ∧
      Source.RelatedLists (Encoding.DeclarationEncoding encoded.equalityId signature symbols)
        named encoded.declarations := by
  obtain ⟨named, _, parsed, encodedRun⟩ := decode_byte_encoding success
  obtain ⟨signature, symbols, encoding⟩ := Encoding.encode_sound encodedRun
  exact ⟨named, signature, symbols, parsed, encoding⟩

/-- This is source transport, not a certificate checker theorem. A subsequent
    preprocessing/checker composition must discharge the numeric refutation. -/
theorem decode_original_unsat {input encoded} (success : decode input = .ok encoded)
    (refuted : ¬ Encoding.ReservedSatisfiable encoded.equalityId encoded.declarations) :
    ¬ NamedQuantifiedEquality.Grammar.BytesSatisfiable (Source.Grammar.spelling input) := by
  obtain ⟨named, _, parsed, encodedRun⟩ := decode_byte_encoding success
  rintro ⟨other, otherParsed, sat⟩
  have same := parsed.unique otherParsed
  cases same
  exact Encoding.encode_unsat encodedRun refuted sat

end Fang.QuantifiedEqualityFrontend
