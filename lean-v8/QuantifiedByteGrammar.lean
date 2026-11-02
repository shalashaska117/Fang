/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import QuantifiedLexing
import QuantifiedUniqueness

namespace Fang.QuantifiedFrontend
open Frontend Source.Grammar

theorem QuantifiedByteTokenization.unique {bytes left right}
    (first : QuantifiedByteTokenization bytes 0 left) (second : QuantifiedByteTokenization bytes 0 right) :
    left = right := by
  obtain ⟨characters, first, firstBytes⟩ := first
  obtain ⟨others, second, secondBytes⟩ := second
  have same : String.ofList characters = String.ofList others := by
    apply spelling_injective
    rw [spelling_ofList_ascii characters first.ascii,
      spelling_ofList_ascii others second.ascii, firstBytes, secondBytes]
  have firstRun := (quantified_tokenize_iff (String.ofList characters) left).mpr (by simpa using first)
  have secondRun := (quantified_tokenize_iff (String.ofList others) right).mpr (by simpa using second)
  rw [same] at firstRun
  exact Except.ok.inj (firstRun.symm.trans secondRun)

end Fang.QuantifiedFrontend

namespace Fang.NamedQuantified.Grammar

/-- The witness contains only the independent lexical and token relations. -/
def Parses (bytes : List UInt8) (named : List Declaration) : Prop :=
  ∃ tokens, QuantifiedFrontend.QuantifiedByteTokenization bytes 0 tokens ∧
    ParsesTokens (tokens.map Frontend.Token.text) named

def BytesSatisfiable (bytes : List UInt8) : Prop :=
  ∃ named, Parses bytes named ∧ Satisfiable named

theorem Parses.unique {bytes left right} (first : Parses bytes left) (second : Parses bytes right) :
    left = right := by
  obtain ⟨leftTokens, leftLexer, leftGrammar⟩ := first
  obtain ⟨rightTokens, rightLexer, rightGrammar⟩ := second
  obtain rfl := leftLexer.unique rightLexer
  exact leftGrammar.unique rightGrammar

end Fang.NamedQuantified.Grammar
