/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.FormulaPrefix
import BodyBridge

namespace Fang.FofTstpPrefix
open TstpText Source.Grammar

theorem read_space (character : Char) (space : Frontend.asciiSpace character = true)
    (rest : List Char) : read (character :: rest) = read rest := by
  simp [read, TstpUnique.readToken, List.dropWhile, space]

theorem empty_prefix_read {input rest} (trace : SourcePrefix input [] rest) :
    read input = read rest := by
  cases trace with
  | empty => rfl
  | whitespace space tail => exact (read_space _ space _).trans (empty_prefix_read tail)
termination_by input.length

/-- Full atom token sequences may end immediately before a FOF operator.
    The explicit boundary excludes accidentally consuming a following argument
    list as part of an intended nullary atom. -/
theorem term_terminal_prefix {tokens value input suffix}
    (parsed : Source.Grammar.TermTokens tokens value [])
    (lexical : SourcePrefix input (tokens.map sourceToken) suffix)
    (noOpening : ∀ rest, TstpUnique.readToken suffix ≠ some (.punctuation '(', rest)) :
    ∃ middle, TstpBody.TermPrefix input value middle ∧ SourcePrefix middle [] suffix := by
  cases parsed with
  | variableTerm name rest =>
    obtain ⟨middle, token, tail⟩ := lexical.head
    exact ⟨middle, .variableTerm token, tail⟩
  | constant name rest noArguments =>
    obtain ⟨middle, token, tail⟩ := lexical.head
    refine ⟨middle, .constant token ?_, tail⟩
    intro after opening
    exact noOpening after (tail.empty_read.symm.trans opening)
  | application name children =>
    obtain ⟨afterName, token, tail⟩ := lexical.head
    obtain ⟨afterOpen, opening, arguments⟩ := tail.head
    obtain ⟨middle, body, remaining⟩ := arguments_prefix children arguments
    exact ⟨middle, .application token opening body, remaining⟩

theorem atom_text_prefix {text : String} {name arguments}
    (parsed : LiteralBytesParse (spelling text) ⟨true, name, arguments⟩)
    (suffix : List Char) (boundary : TstpUnique.WordBoundary suffix)
    (noOpening : ∀ rest, read suffix ≠ some (.base (.punctuation '('), rest)) :
    ∃ middle, FormulaPrefix (text.toList ++ suffix) (.atom name arguments) middle ∧
      read middle = read suffix := by
  obtain ⟨tokens, lexical, parsed⟩ := parsed
  cases parsed with
  | positive atom =>
    have chars : (spelling text).map byteChar = text.toList :=
      spelling_chars text lexical.ascii
    have noOldOpening : ∀ rest, TstpUnique.readToken suffix ≠ some (.punctuation '(', rest) := by
      intro rest opening
      exact noOpening rest (read_old opening)
    obtain ⟨middle, body, remaining⟩ := term_terminal_prefix atom
      (source_tokenization lexical suffix boundary) noOldOpening
    exact ⟨middle, .atom (by simpa only [chars] using body), empty_prefix_read remaining⟩

theorem FormulaPrefix.whitespace {input value rest}
    (parsed : FormulaPrefix input value rest) (character : Char)
    (space : Frontend.asciiSpace character = true) : FormulaPrefix (character :: input) value rest := by
  cases parsed with
  | atom body =>
    cases body with
    | constant token noArguments =>
      exact .atom (.constant ((readToken_space character space _).trans token) noArguments)
    | application token opening children =>
      exact .atom (.application ((readToken_space character space _).trans token) opening children)
  | truth token => exact .truth ((read_space character space _).trans token)
  | falsity token => exact .falsity ((read_space character space _).trans token)
  | neg sign opening child closing => exact .neg ((read_space character space _).trans sign) opening child closing
  | binary op opening first operator second closing =>
    exact .binary op ((read_space character space _).trans opening) first operator second closing

end Fang.FofTstpPrefix
