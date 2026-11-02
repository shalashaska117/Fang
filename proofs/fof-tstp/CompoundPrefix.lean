/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.PrefixBridge

namespace Fang.FofTstpPrefix

def PrefixPrintable (text : String) (value : NamedFOF.Formula) : Prop :=
  ∀ suffix, TstpUnique.WordBoundary suffix →
    (∀ rest, read suffix ≠ some (.base (.punctuation '('), rest)) →
    ∃ middle, FormulaPrefix (text.toList ++ suffix) value middle ∧
      read middle = read suffix

private theorem punctuation (character : Char) (valid : character ∈ TstpUnique.punctuation)
    (suffix : List Char) : read (character :: suffix) = some (.base (.punctuation character), suffix) :=
  read_old (TstpUnique.readToken_punctuation character valid suffix)

private theorem excludes_opening {input token suffix}
    (accepted : read input = some (token, suffix))
    (different : token ≠ .base (.punctuation '(')) :
    ∀ rest, read input ≠ some (.base (.punctuation '('), rest) := by
  intro rest other
  exact different (read_unique accepted other).1

private theorem space_boundary (suffix : List Char) : TstpUnique.WordBoundary (' ' :: suffix) := by
  intro character rest same
  cases same
  decide

def Connective.characters : Connective → List Char
  | .conjunction => ['&']
  | .disjunction => ['|']
  | .implication => ['=', '>']

theorem read_operator (op : Connective) (suffix : List Char) :
    read (' ' :: (op.characters ++ (' ' :: suffix))) = some (op.token, ' ' :: suffix) := by
  rw [read_space ' ' (by decide)]
  cases op with
  | conjunction => exact read_conjunction _
  | disjunction => exact punctuation '|' (by decide) _
  | implication => exact read_implication _

private theorem binary_prefix (op : Connective) {leftText rightText left right}
    (first : PrefixPrintable leftText left) (second : PrefixPrintable rightText right)
    (suffix : List Char) :
    FormulaPrefix
      ('(' :: (leftText.toList ++ (' ' :: (op.characters ++ (' ' :: (rightText.toList ++ (')' :: suffix)))))))
      (op.formula left right) suffix := by
  obtain ⟨afterLeft, leftParse, leftRead⟩ := first
    (' ' :: (op.characters ++ (' ' :: (rightText.toList ++ (')' :: suffix)))))
    (space_boundary _)
    (excludes_opening (read_operator op _) (by cases op <;> decide))
  obtain ⟨afterRight, rightParse, rightRead⟩ := second (')' :: suffix)
    (TstpUnique.punctuation_boundary ')' (by decide) _)
    (excludes_opening (punctuation ')' (by decide) _) (by decide))
  exact .binary op (punctuation '(' (by decide) _) leftParse
    (leftRead.trans (read_operator op _))
    (rightParse.whitespace ' ' (by decide))
    (rightRead.trans (punctuation ')' (by decide) _))

/-- Every body printed by the formula grammar is consumed with its intended
    meaning. A suffix boundary prevents a nullary atom from absorbing another
    argument list. Whitespace before the suffix may remain unconsumed. -/
theorem formula_text_prefix {text value} (grammar : FofTstpText.FormulaText text value) :
    PrefixPrintable text value := by
  induction grammar with
  | atom body => exact atom_text_prefix body
  | truth =>
    intro suffix boundary _
    exact ⟨suffix, .truth (read_truth suffix boundary), rfl⟩
  | falsity =>
    intro suffix boundary _
    exact ⟨suffix, .falsity (read_old (TstpUnique.readToken_word "$false".toList suffix
      .falseLiteral (by decide) (by decide) boundary (by decide))), rfl⟩
  | neg child ih =>
    intro suffix _ _
    obtain ⟨middle, parsed, token⟩ := ih (')' :: suffix)
      (TstpUnique.punctuation_boundary ')' (by decide) _)
      (excludes_opening (punctuation ')' (by decide) _) (by decide))
    refine ⟨suffix, ?_, rfl⟩
    have result := FormulaPrefix.neg (punctuation '~' (by decide) _)
      (punctuation '(' (by decide) _) parsed
      (token.trans (punctuation ')' (by decide) _))
    simpa only [String.toList_append, List.append_assoc,
      show "~(".toList = ['~', '('] from by decide,
      show ")".toList = [')'] from by decide, List.cons_append, List.nil_append] using result
  | conj first second leftIH rightIH =>
    intro suffix _ _
    refine ⟨suffix, ?_, rfl⟩
    simpa only [String.toList_append, List.append_assoc, Connective.characters, Connective.formula,
      show "(".toList = ['('] from by decide, show ")".toList = [')'] from by decide,
      show " & ".toList = [' ', '&', ' '] from by decide, List.cons_append, List.nil_append]
      using binary_prefix .conjunction leftIH rightIH suffix
  | disj first second leftIH rightIH =>
    intro suffix _ _
    refine ⟨suffix, ?_, rfl⟩
    simpa only [String.toList_append, List.append_assoc, Connective.characters, Connective.formula,
      show "(".toList = ['('] from by decide, show ")".toList = [')'] from by decide,
      show " | ".toList = [' ', '|', ' '] from by decide, List.cons_append, List.nil_append]
      using binary_prefix .disjunction leftIH rightIH suffix
  | implies first second leftIH rightIH =>
    intro suffix _ _
    refine ⟨suffix, ?_, rfl⟩
    simpa only [String.toList_append, List.append_assoc, Connective.characters, Connective.formula,
      show "(".toList = ['('] from by decide, show ")".toList = [')'] from by decide,
      show " => ".toList = [' ', '=', '>', ' '] from by decide, List.cons_append, List.nil_append]
      using binary_prefix .implication leftIH rightIH suffix

theorem printed_formula_prefix {problem value text}
    (printed : FofTstpExport.formula problem value = .ok text)
    (suffix : List Char) (boundary : TstpUnique.WordBoundary suffix)
    (noOpening : ∀ rest, read suffix ≠ some (.base (.punctuation '('), rest)) :
    ∃ named middle, FofTstpText.NamedFormula problem value named ∧
      FormulaPrefix (text.toList ++ suffix) named middle ∧ read middle = read suffix := by
  obtain ⟨named, relation, grammar⟩ := FofTstpText.formula_correspondence value printed
  obtain ⟨middle, parsed, token⟩ := formula_text_prefix grammar suffix boundary noOpening
  exact ⟨named, middle, relation, parsed, token⟩

end Fang.FofTstpPrefix
