/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFFormulaUniqueness

namespace Fang.FOFFrontend
open Frontend Source.Grammar

theorem FofByteTokenization.unique {bytes left right}
    (first : FofByteTokenization bytes 0 left) (second : FofByteTokenization bytes 0 right) :
    left = right := by
  obtain ⟨characters, first, firstBytes⟩ := first
  obtain ⟨others, second, secondBytes⟩ := second
  have same : String.ofList characters = String.ofList others := by
    apply spelling_injective
    rw [spelling_ofList_ascii characters first.ascii,
      spelling_ofList_ascii others second.ascii, firstBytes, secondBytes]
  have firstRun := (fof_tokenize_iff (String.ofList characters) left).mpr (by simpa using first)
  have secondRun := (fof_tokenize_iff (String.ofList others) right).mpr (by simpa using second)
  rw [same] at firstRun
  exact Except.ok.inj (firstRun.symm.trans secondRun)

end Fang.FOFFrontend

namespace Fang.FOFGrammar

theorem Parses.unique {bytes left right} (first : Parses bytes left) (second : Parses bytes right) :
    left = right := by
  obtain ⟨leftTokens, leftLexer, leftGrammar, _⟩ := first
  obtain ⟨rightTokens, rightLexer, rightGrammar, _⟩ := second
  obtain rfl := leftLexer.unique rightLexer
  exact leftGrammar.unique rightGrammar

end Fang.FOFGrammar

namespace Fang.FOFFrontend
open Frontend FOFGrammar

theorem decode_prepared_satisfiable_iff {input decoded} (success : decode input = .ok decoded) :
    BytesSatisfiable (Source.Grammar.spelling input) ↔
      Fang.Satisfiable (GroundFOF.prepareDeclarations decoded.declarations) := by
  obtain ⟨named, parsed, encoding⟩ := decode_byte_grammar success
  constructor
  · rintro ⟨other, otherParsed, model⟩
    obtain rfl := parsed.unique otherParsed
    exact encoding.prepared_satisfiable_iff.mp model
  · intro model
    exact ⟨named, parsed, encoding.prepared_satisfiable_iff.mpr model⟩

theorem decode_check_original_unsat {input decoded} (success : decode input = .ok decoded)
    (certificate : Fang.Certificate)
    (accepted : Fang.check (GroundFOF.prepareDeclarations decoded.declarations) certificate = true) :
    ¬ BytesSatisfiable (Source.Grammar.spelling input) := by
  intro model
  exact Fang.check_sound _ _ accepted ((decode_prepared_satisfiable_iff success).mp model)

end Fang.FOFFrontend
