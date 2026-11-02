/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import CnfBooleanInput
import FofTermSound

namespace Fang.TptpCandidate.FullFof.CnfBoolean
open Grammar

inductive AtomicTokens : List Token → Formula → List Token → Prop where
  | truth {token rest} (value : token.kind = .legacy .truth) : AtomicTokens (token :: rest) .truth rest
  | falsity {token rest} (value : token.kind = .legacy .falsity) : AtomicTokens (token :: rest) .falsity rest
  | ordinary {input value rest} (parsed : AtomTokens input value rest) : AtomicTokens input value rest

theorem atomic_sound {endOffset input value rest}
    (success : atomic endOffset input = .ok (value, rest)) : AtomicTokens input value rest := by
  unfold atomic at success
  repeat' first | contradiction | split at success
  · rename_i token tail shape kind
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
    exact .truth kind
  · rename_i token tail shape kind
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
    exact .falsity kind
  · exact .ordinary (atom_sound success)

inductive WrappedAtomicTokens : List Token → Formula → List Token → Prop where
  | bare {input value rest} (atom : AtomicTokens input value rest) : WrappedAtomicTokens input value rest
  | paren {opening input value closing rest} (left : Punct opening '(')
      (atom : AtomicTokens input value (closing :: rest)) (right : Punct closing ')') :
      WrappedAtomicTokens (opening :: input) value rest

inductive LiteralTokens : List Token → Formula → List Token → Prop where
  | positive {input value rest} (atom : AtomicTokens input value rest) : LiteralTokens input value rest
  | negative {token input value rest} (negative : Punct token '~')
      (atom : WrappedAtomicTokens input value rest) (atomic : IsAtomic value) :
      LiteralTokens (token :: input) (.neg value) rest

inductive DisjunctionTokens : List Token → List Formula → List Token → Prop where
  | one {input value rest} (first : LiteralTokens input value rest)
      (notBar : isChar '|' rest = false) : DisjunctionTokens input [value] rest
  | more {input value separator middle values rest}
      (first : LiteralTokens input value (separator :: middle)) (bar : Punct separator '|')
      (tail : DisjunctionTokens middle values rest) : DisjunctionTokens input (value :: values) rest

inductive ClauseTokens : List Token → List Formula → List Token → Prop where
  | bare {input values rest} (body : DisjunctionTokens input values rest) : ClauseTokens input values rest
  | paren {opening input values closing rest} (left : Punct opening '(')
      (body : ClauseTokens input values (closing :: rest)) (right : Punct closing ')') :
      ClauseTokens (opening :: input) values rest

theorem negate_sound {endOffset tokens body value}
    (success : negate endOffset tokens body = .ok value) : IsAtomic body ∧ value = .neg body := by
  cases body <;> simp_all [negate, failure, IsAtomic]

theorem wrappedAtom_sound {endOffset input value final}
    (success : wrappedAtom endOffset input = .ok (value, final)) :
    WrappedAtomicTokens input value final := by
  unfold wrappedAtom at success
  simp only [bind, Except.bind, pure, Except.pure] at success
  repeat' first | contradiction | split at success
  · rename_i opened _ first firstAt _ closing closingAt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
    obtain ⟨token, rest, inputShape, kind⟩ := isChar_exact opened
    have closeShape := expect_exact closingAt
    have parsed := atomic_sound firstAt
    rw [inputShape] at parsed ⊢
    rw [closeShape.1] at parsed
    exact .paren kind (by simpa using parsed) closeShape.2
  · exact .bare (atomic_sound success)

theorem literal_sound {endOffset input value final}
    (success : literal endOffset input = .ok (value, final)) : LiteralTokens input value final := by
  unfold literal at success
  simp only [failure, bind, Except.bind, pure, Except.pure] at success
  repeat' first | contradiction | split at success
  · rename_i negative notQuantified _ first firstAt _ output outputAt
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
    have negated := negate_sound outputAt
    obtain ⟨token, rest, inputShape, kind⟩ := isChar_exact negative
    have parsed := wrappedAtom_sound firstAt
    rw [negated.2, inputShape]
    rw [inputShape] at parsed
    exact .negative kind (by simpa using parsed) negated.1
  · exact .positive (atomic_sound success)

theorem disjunction_sound {fuel endOffset input values final}
    (success : disjunction fuel endOffset input = .ok (values, final)) :
    DisjunctionTokens input values final := by
  induction fuel generalizing input values final with
  | zero => simp [disjunction, failure] at success
  | succ fuel ih =>
    simp only [disjunction, failure, bind, Except.bind, pure, Except.pure] at success
    repeat' first | contradiction | split at success
    · rename_i _ first firstAt bar _ tail tailAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      obtain ⟨separator, rest, shape, separatorAt⟩ := isChar_exact bar
      have parsed := literal_sound firstAt
      rw [shape] at parsed tailAt
      exact .more parsed separatorAt (ih (by simpa using tailAt))
    · rename_i _ first firstAt notBar notOther
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      exact .one (literal_sound firstAt) (by simpa using notBar)

theorem clause_sound {fuel depth endOffset input values final}
    (success : clause fuel depth endOffset input = .ok (values, final)) :
    ClauseTokens input values final := by
  induction fuel generalizing depth input values final with
  | zero => simp [clause, failure] at success
  | succ fuel ih =>
    simp only [clause, failure, bind, Except.bind, pure, Except.pure] at success
    repeat' first | contradiction | split at success
    · rename_i withinDepth opened _ first firstAt _ closing closingAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      obtain ⟨token, rest, inputShape, kind⟩ := isChar_exact opened
      have closeShape := expect_exact closingAt
      have parsed := ih firstAt
      rw [inputShape] at parsed ⊢
      rw [closeShape.1] at parsed
      exact .paren kind (by simpa using parsed) closeShape.2
    · exact .bare (disjunction_sound success)

end Fang.TptpCandidate.FullFof.CnfBoolean
