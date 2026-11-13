/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import AnnotationLexer

namespace Fang.FofTstpPrefix

/-- Extend the existing annotation lexer only where it rejects a FOF token.
    Existing token values and unconsumed suffixes are preserved exactly. -/
inductive Token where
  | base : TstpUnique.Token → Token
  | truth
  | conjunction
  | implication
  deriving DecidableEq, Repr

def read (input : List Char) : Option (Token × List Char) :=
  match TstpUnique.readToken input with
  | some (token, rest) => some (.base token, rest)
  | none =>
    let chars := input.dropWhile Frontend.asciiSpace
    match chars with
    | '&' :: rest => some (.conjunction, rest)
    | '=' :: '>' :: rest => some (.implication, rest)
    | _ =>
      let (word, rest) := chars.span Frontend.wordChar
      if String.ofList word = "$true" then some (.truth, rest) else none

theorem read_old {input token rest}
    (accepted : TstpUnique.readToken input = some (token, rest)) :
    read input = some (.base token, rest) := by simp [read, accepted]

theorem read_unique {input left right leftRest rightRest}
    (first : read input = some (left, leftRest))
    (second : read input = some (right, rightRest)) : left = right ∧ leftRest = rightRest :=
  Prod.mk.inj (Option.some.inj (first.symm.trans second))

theorem read_conjunction (suffix : List Char) :
    read ('&' :: suffix) = some (.conjunction, suffix) := by rfl

theorem read_implication (suffix : List Char) :
    read ('=' :: '>' :: suffix) = some (.implication, suffix) := by rfl

theorem read_truth (suffix : List Char) (boundary : TstpUnique.WordBoundary suffix) :
    read ("$true".toList ++ suffix) = some (.truth, suffix) := by
  have span := TstpUnique.span_prefix Frontend.wordChar "$true".toList suffix
    (by decide) boundary
  have old : TstpUnique.readToken ("$true".toList ++ suffix) = none := by
    change (do
      let token ← TstpUnique.classifyWord (("$true".toList ++ suffix).span Frontend.wordChar).1
      some (token, (("$true".toList ++ suffix).span Frontend.wordChar).2)) = none
    rw [span]
    have classified : TstpUnique.classifyWord "$true".toList = none := by decide
    rw [classified]
    rfl
  simp only [read, old]
  change (if String.ofList (("$true".toList ++ suffix).span Frontend.wordChar).1 = "$true"
    then some (Token.truth, (("$true".toList ++ suffix).span Frontend.wordChar).2) else none) = _
  rw [span]
  simp

theorem truth_requires_word_boundary : read "$truex".toList = none := by decide
theorem implication_requires_both_chars : read "=p".toList = none := by decide

end Fang.FofTstpPrefix
