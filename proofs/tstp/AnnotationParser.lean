/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import AnnotationLexer

namespace Fang.TstpUnique
open Fang.TstpText

inductive Closing where
  | paren | bracket
  deriving DecidableEq

def Closing.char : Closing → Char
  | .paren => ')'
  | .bracket => ']'

mutual
inductive ParsedData : List Char → Datum → List Char → Prop where
  | atom {input rest name}
      (head : readToken input = some (.atom name, rest))
      (noArguments : ∀ tail, readToken rest ≠ some (.punctuation '(', tail)) :
      ParsedData input (.atom name) rest
  | natural {input rest value} (head : readToken input = some (.natural value, rest)) :
      ParsedData input (.natural value) rest
  | function {input middle childrenInput rest name values}
      (head : readToken input = some (.atom name, middle))
      (opening : readToken middle = some (.punctuation '(', childrenInput))
      (children : ParsedItems childrenInput values rest .paren) :
      ParsedData input (.function name values) rest
  | emptyList {input middle rest}
      (opening : readToken input = some (.punctuation '[', middle))
      (closing : readToken middle = some (.punctuation ']', rest)) :
      ParsedData input (.list []) rest
  | list {input middle rest values}
      (opening : readToken input = some (.punctuation '[', middle))
      (children : ParsedItems middle values rest .bracket) :
      ParsedData input (.list values) rest
inductive ParsedItems : List Char → List Datum → List Char → Closing → Prop where
  | last {input middle rest value closing}
      (head : ParsedData input value middle)
      (endToken : readToken middle = some (.punctuation closing.char, rest)) :
      ParsedItems input [value] rest closing
  | more {input middle tailInput rest value values closing}
      (head : ParsedData input value middle)
      (comma : readToken middle = some (.punctuation ',', tailInput))
      (tail : ParsedItems tailInput values rest closing) :
      ParsedItems input (value :: values) rest closing
end

theorem readToken_unique {input left right leftRest rightRest}
    (first : readToken input = some (left, leftRest))
    (second : readToken input = some (right, rightRest)) :
    left = right ∧ leftRest = rightRest :=
  Prod.mk.inj (Option.some.inj (first.symm.trans second))

theorem ParsedData.not_closing {input value rest} (parsed : ParsedData input value rest)
    (closing : Closing) (suffix : List Char) :
    readToken input ≠ some (.punctuation closing.char, suffix) := by
  intro other
  cases parsed with
  | atom head noArguments => cases (readToken_unique head other).1
  | natural head => cases (readToken_unique head other).1
  | function head opening children => cases (readToken_unique head other).1
  | emptyList opening endToken =>
    have impossible := (readToken_unique opening other).1
    cases closing <;> cases impossible
  | list opening children =>
    have impossible := (readToken_unique opening other).1
    cases closing <;> cases impossible

theorem ParsedItems.not_closing {input values rest close} (parsed : ParsedItems input values rest close)
    (closing : Closing) (suffix : List Char) :
    readToken input ≠ some (.punctuation closing.char, suffix) := by
  cases parsed with
  | last head endToken => exact head.not_closing closing suffix
  | more head comma tail => exact head.not_closing closing suffix

mutual
theorem ParsedData.unique {input left right leftRest rightRest}
    (first : ParsedData input left leftRest) (second : ParsedData input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | atom head noArguments =>
    cases second with
    | atom other noOther =>
      obtain ⟨same, rest⟩ := readToken_unique head other
      cases same
      exact ⟨rfl, rest⟩
    | natural other => cases (readToken_unique head other).1
    | function other opening children =>
      obtain ⟨same, rest⟩ := readToken_unique head other
      cases rest
      exact False.elim (noArguments _ opening)
    | emptyList other closing => cases (readToken_unique head other).1
    | list other children => cases (readToken_unique head other).1
  | natural head =>
    cases second with
    | atom other noOther => cases (readToken_unique head other).1
    | natural other =>
      obtain ⟨same, rest⟩ := readToken_unique head other
      cases same
      exact ⟨rfl, rest⟩
    | function other opening children => cases (readToken_unique head other).1
    | emptyList other closing => cases (readToken_unique head other).1
    | list other children => cases (readToken_unique head other).1
  | function head opening children =>
    cases second with
    | atom other noOther =>
      obtain ⟨same, rest⟩ := readToken_unique head other
      cases rest
      exact False.elim (noOther _ opening)
    | natural other => cases (readToken_unique head other).1
    | function other otherOpening otherChildren =>
      obtain ⟨same, middle⟩ := readToken_unique head other
      cases same
      cases middle
      have sameInput := (readToken_unique opening otherOpening).2
      cases sameInput
      obtain ⟨sameValues, sameRest⟩ := children.unique otherChildren
      cases sameValues
      exact ⟨rfl, sameRest⟩
    | emptyList other closing => cases (readToken_unique head other).1
    | list other children => cases (readToken_unique head other).1
  | emptyList opening closing =>
    cases second with
    | atom other noOther => cases (readToken_unique opening other).1
    | natural other => cases (readToken_unique opening other).1
    | function other otherOpening children => cases (readToken_unique opening other).1
    | emptyList other otherClosing =>
      have sameInput := (readToken_unique opening other).2
      cases sameInput
      exact ⟨rfl, (readToken_unique closing otherClosing).2⟩
    | list other children =>
      have sameInput := (readToken_unique opening other).2
      cases sameInput
      exact False.elim (children.not_closing .bracket _ closing)
  | list opening children =>
    cases second with
    | atom other noOther => cases (readToken_unique opening other).1
    | natural other => cases (readToken_unique opening other).1
    | function other otherOpening otherChildren => cases (readToken_unique opening other).1
    | emptyList other otherClosing =>
      have sameInput := (readToken_unique opening other).2
      cases sameInput
      exact False.elim (children.not_closing .bracket _ otherClosing)
    | list other otherChildren =>
      have sameInput := (readToken_unique opening other).2
      cases sameInput
      obtain ⟨sameValues, sameRest⟩ := children.unique otherChildren
      cases sameValues
      exact ⟨rfl, sameRest⟩
theorem ParsedItems.unique {input left right leftRest rightRest close}
    (first : ParsedItems input left leftRest close) (second : ParsedItems input right rightRest close) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | last head endToken =>
    cases second with
    | last other otherEnd =>
      obtain ⟨sameValue, sameMiddle⟩ := head.unique other
      cases sameValue
      cases sameMiddle
      exact ⟨rfl, (readToken_unique endToken otherEnd).2⟩
    | more other comma tail =>
      have sameMiddle := (head.unique other).2
      cases sameMiddle
      have impossible := (readToken_unique endToken comma).1
      cases close <;> cases impossible
  | more head comma tail =>
    cases second with
    | last other otherEnd =>
      have sameMiddle := (head.unique other).2
      cases sameMiddle
      have impossible := (readToken_unique comma otherEnd).1
      cases close <;> cases impossible
    | more other otherComma otherTail =>
      obtain ⟨sameValue, sameMiddle⟩ := head.unique other
      cases sameValue
      cases sameMiddle
      have sameTail := (readToken_unique comma otherComma).2
      cases sameTail
      obtain ⟨sameValues, sameRest⟩ := tail.unique otherTail
      cases sameValues
      exact ⟨rfl, sameRest⟩
end

end Fang.TstpUnique
