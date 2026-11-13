/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.PrefixLexer
import BodyPrefix
import Fang.FOF.TSTP.FormulaText

namespace Fang.FofTstpPrefix

inductive Connective where
  | conjunction | disjunction | implication

def Connective.token : Connective → Token
  | .conjunction => .conjunction
  | .disjunction => .base (.punctuation '|')
  | .implication => .implication

def Connective.formula : Connective → NamedFOF.Formula → NamedFOF.Formula → NamedFOF.Formula
  | .conjunction => .conj
  | .disjunction => .disj
  | .implication => .implies

theorem Connective.token_injective {left right : Connective} (same : left.token = right.token) :
    left = right := by cases left <;> cases right <;> simp_all [Connective.token]

/-- Consuming grammar for Fang's fully parenthesized FOF bodies. The suffix is
    explicit so a proof-row parser can distinguish formula and metadata text. -/
inductive FormulaPrefix : List Char → NamedFOF.Formula → List Char → Prop where
  | atom {input name arguments rest}
      (body : TstpBody.TermPrefix input (.app name arguments) rest) :
      FormulaPrefix input (.atom name arguments) rest
  | truth {input rest} (token : read input = some (.truth, rest)) :
      FormulaPrefix input .truth rest
  | falsity {input rest} (token : read input = some (.base .falseLiteral, rest)) :
      FormulaPrefix input .falsity rest
  | neg {input afterSign inside afterBody rest body}
      (sign : read input = some (.base (.punctuation '~'), afterSign))
      (opening : read afterSign = some (.base (.punctuation '('), inside))
      (child : FormulaPrefix inside body afterBody)
      (closing : read afterBody = some (.base (.punctuation ')'), rest)) :
      FormulaPrefix input (.neg body) rest
  | binary (op : Connective) {input inside afterLeft middle afterRight rest left right}
      (opening : read input = some (.base (.punctuation '('), inside))
      (first : FormulaPrefix inside left afterLeft)
      (operator : read afterLeft = some (op.token, middle))
      (second : FormulaPrefix middle right afterRight)
      (closing : read afterRight = some (.base (.punctuation ')'), rest)) :
      FormulaPrefix input (op.formula left right) rest

theorem atom_read {input name arguments rest}
    (body : TstpBody.TermPrefix input (.app name arguments) rest) :
    ∃ after, read input = some (.base (.atom name), after) := by
  cases body with
  | constant token noArguments => exact ⟨_, read_old token⟩
  | application token opening children => exact ⟨_, read_old token⟩

theorem FormulaPrefix.unique {input left right leftRest rightRest}
    (first : FormulaPrefix input left leftRest) (second : FormulaPrefix input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction first generalizing right rightRest with
  | atom body =>
    obtain ⟨after, token⟩ := atom_read body
    cases second with
    | atom other =>
      obtain ⟨same, suffix⟩ := body.unique other
      obtain ⟨rfl, rfl⟩ := Source.Term.app.inj same
      exact ⟨rfl, suffix⟩
    | truth other => cases (read_unique token other).1
    | falsity other => cases (read_unique token other).1
    | neg other _ _ _ => cases (read_unique token other).1
    | binary _ other _ _ _ _ => cases (read_unique token other).1
  | truth token =>
    cases second with
    | atom other =>
      obtain ⟨after, head⟩ := atom_read other
      cases (read_unique token head).1
    | truth other => exact ⟨rfl, (read_unique token other).2⟩
    | falsity other => cases (read_unique token other).1
    | neg other _ _ _ => cases (read_unique token other).1
    | binary _ other _ _ _ _ => cases (read_unique token other).1
  | falsity token =>
    cases second with
    | atom other =>
      obtain ⟨after, head⟩ := atom_read other
      cases (read_unique token head).1
    | truth other => cases (read_unique token other).1
    | falsity other => exact ⟨rfl, (read_unique token other).2⟩
    | neg other _ _ _ => cases (read_unique token other).1
    | binary _ other _ _ _ _ => cases (read_unique token other).1
  | neg sign opening child closing ih =>
    cases second with
    | atom other =>
      obtain ⟨after, head⟩ := atom_read other
      cases (read_unique sign head).1
    | truth other => cases (read_unique sign other).1
    | falsity other => cases (read_unique sign other).1
    | binary _ other _ _ _ _ => cases (read_unique sign other).1
    | neg otherSign otherOpen otherChild otherClose =>
      have same := (read_unique sign otherSign).2
      cases same
      have same := (read_unique opening otherOpen).2
      cases same
      obtain ⟨sameBody, sameSuffix⟩ := ih otherChild
      cases sameSuffix
      exact ⟨congrArg NamedFOF.Formula.neg sameBody, (read_unique closing otherClose).2⟩
  | binary op opening first operator rightChild closing leftIH rightIH =>
    cases second with
    | atom other =>
      obtain ⟨after, head⟩ := atom_read other
      cases (read_unique opening head).1
    | truth other => cases (read_unique opening other).1
    | falsity other => cases (read_unique opening other).1
    | neg other _ _ _ => cases (read_unique opening other).1
    | binary otherOp otherOpen otherFirst otherOperator otherSecond otherClose =>
      have same := (read_unique opening otherOpen).2
      cases same
      obtain ⟨sameLeft, sameSuffix⟩ := leftIH otherFirst
      cases sameSuffix
      obtain ⟨sameOp, sameMiddle⟩ := read_unique operator otherOperator
      have sameOp := Connective.token_injective sameOp
      cases sameOp
      cases sameMiddle
      obtain ⟨sameRight, sameEnd⟩ := rightIH otherSecond
      cases sameEnd
      cases sameLeft
      cases sameRight
      exact ⟨rfl, (read_unique closing otherClose).2⟩

end Fang.FofTstpPrefix
