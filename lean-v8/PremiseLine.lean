/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The premise line a certificate may begin with: `(premises (item F S) ...)`, naming bundle items as `--goals` prints them, then a line break and the version-8 certificate. The parser reads characters and accepts only the canonical form: one space before each item, one space between the two numbers, no leading zeros, and the closing parenthesis right after the last item. Soundness does not depend on this parser, since the cited entries accept any item list; the controls show which lines are accepted and which are refused. -/

namespace Fang.TptpCandidate.Roles.Bundle.PremiseLine

/-- The value of a list of decimal digits. -/
def digitsValue (digits : List Char) : Nat :=
  digits.foldl (fun value digit => 10 * value + (digit.toNat - '0'.toNat)) 0

/-- A natural number without leading zeros, and the characters after it. -/
def number : List Char → Option (Nat × List Char)
  | [] => none
  | first :: rest =>
    if first.isDigit then
      let (more, after) := rest.span Char.isDigit
      if first == '0' && !more.isEmpty then none else some (digitsValue (first :: more), after)
    else none

/-- The items of a premise line after `(premises`, up to its closing parenthesis, which must end the line. -/
def items : Nat → List Char → Option (List (Nat × Nat))
  | 0, _ => none
  | _ + 1, [')'] => some []
  | fuel + 1, ' ' :: '(' :: 'i' :: 't' :: 'e' :: 'm' :: ' ' :: rest => do
    let (file, rest) ← number rest
    let ' ' :: rest := rest | none
    let (statement, rest) ← number rest
    let ')' :: rest := rest | none
    let tail ← items fuel rest
    pure ((file, statement) :: tail)
  | _, _ => none

/-- `none` without a premise line; otherwise the cited items and the characters of the certificate after the line break, or `.error ()` for a line that is not in canonical form or is not followed by a line break. -/
def split (proof : String) : Option (Except Unit (List (Nat × Nat) × List Char)) :=
  match proof.toList with
  | '(' :: 'p' :: 'r' :: 'e' :: 'm' :: 'i' :: 's' :: 'e' :: 's' :: line =>
    let (head, tail) := line.span (· != '\n')
    match tail with
    | '\n' :: rest =>
      match items (head.length + 1) head with
      | some cited => some (.ok (cited, rest))
      | none => some (.error ())
    | _ => some (.error ())
  | _ => none

/-- The items and certificate characters of an accepted line, for the controls. -/
def accepted (proof : String) : Option (List (Nat × Nat) × List Char) :=
  match split proof with
  | some (.ok result) => some result
  | _ => none

/-- Whether a premise line is present and refused, for the controls. -/
def refused (proof : String) : Bool :=
  match split proof with
  | some (.error ()) => true
  | _ => false

/-- Accepted: the canonical line, and the certificate after it unchanged. -/
theorem canonical_accepted :
    accepted "(premises (item 0 12) (item 1 7))\n(fang-proof 8\n  x)\n" ==
      some ([(0, 12), (1, 7)], "(fang-proof 8\n  x)\n".toList) := by
  cbv

/-- Accepted: an empty citation list. -/
theorem empty_accepted : accepted "(premises)\nC" == some ([], "C".toList) := by
  cbv

/-- No premise line: the certificate is used whole. -/
theorem absent : (split "(fang-proof 8\n  x)\n").isNone := by
  cbv

/-- Refused: a double space. -/
theorem extra_space_refused : refused "(premises  (item 0 12))\nC" := by
  cbv

/-- Refused: a word other than `item`. -/
theorem other_word_refused : refused "(premises (axiom 0 12))\nC" := by
  cbv

/-- Refused: a non-numeric index. -/
theorem non_numeric_refused : refused "(premises (item 0 x))\nC" := by
  cbv

/-- Refused: a leading zero. -/
theorem leading_zero_refused : refused "(premises (item 0 012))\nC" := by
  cbv

/-- Refused: text after the closing parenthesis. -/
theorem trailing_text_refused : refused "(premises (item 0 12)) x\nC" := by
  cbv

/-- Refused: a premise line without a line break after it. -/
theorem no_certificate_refused : refused "(premises (item 0 12))" := by
  cbv

#print axioms Fang.TptpCandidate.Roles.Bundle.PremiseLine.canonical_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.PremiseLine.empty_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.PremiseLine.absent
#print axioms Fang.TptpCandidate.Roles.Bundle.PremiseLine.extra_space_refused
#print axioms Fang.TptpCandidate.Roles.Bundle.PremiseLine.other_word_refused
#print axioms Fang.TptpCandidate.Roles.Bundle.PremiseLine.non_numeric_refused
#print axioms Fang.TptpCandidate.Roles.Bundle.PremiseLine.leading_zero_refused
#print axioms Fang.TptpCandidate.Roles.Bundle.PremiseLine.trailing_text_refused
#print axioms Fang.TptpCandidate.Roles.Bundle.PremiseLine.no_certificate_refused

end Fang.TptpCandidate.Roles.Bundle.PremiseLine
