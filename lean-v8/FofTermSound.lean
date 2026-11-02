/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Adapt the Fang named-CNF structural proof to the scoped FOF parser and
   its independent productions. Successful parsing is the only premise. -/
import FofGrammarTypes

namespace Fang.TptpCandidate
deriving instance ReflBEq, LawfulBEq for Kind
namespace FullFof
deriving instance ReflBEq, LawfulBEq for Kind
open Grammar

theorem expect_exact {char endOffset tokens token rest}
    (success : expect char endOffset tokens = .ok (token, rest)) :
    tokens = token :: rest ∧ Punct token char := by
  cases tokens with
  | nil => simp [expect, failure] at success
  | cons first tail =>
    by_cases matched : first.kind = .legacy (.punctuation char)
    · simp [expect, matched] at success
      rcases success with ⟨rfl, rfl⟩
      exact ⟨rfl, matched⟩
    · simp [expect, matched, failure] at success

theorem isChar_exact {char tokens} (success : isChar char tokens = true) :
    ∃ token rest, tokens = token :: rest ∧ Punct token char := by
  cases tokens with
  | nil => simp [isChar] at success
  | cons token rest =>
    exact ⟨token, rest, rfl, by simpa [isChar, Punct] using success⟩

theorem term_arguments_sound (fuel : Nat) :
    (∀ depth scope endOffset input value rest,
      term fuel depth scope endOffset input = .ok (value, rest) → TermTokens input value rest) ∧
    (∀ depth scope endOffset input values rest,
      arguments fuel depth scope endOffset input = .ok (values, rest) →
        ArgumentsTokens input values rest) := by
  induction fuel with
  | zero =>
    constructor
    · intro depth scope endOffset input value rest success
      simp [term, failure] at success
    · intro depth scope endOffset input values rest success
      simp [arguments, failure] at success
  | succ fuel ih =>
    constructor
    · intro depth scope endOffset input value final success
      by_cases large : depth > 64
      · simp [term, large, failure, bind, Except.bind] at success
      · cases input with
        | nil => simp [term, large, failure] at success
        | cons token rest =>
          cases kindAt : token.kind with
          | legacy old =>
            cases old with
            | «variable» label =>
              have same : value = .var label ∧ final = rest := by
                cases scope with
                | none => simpa [term, large, kindAt, pure, Except.pure] using success.symm
                | some bound =>
                  by_cases member : label ∈ bound
                  · simpa [term, large, kindAt, member, bind, Except.bind,
                      pure, Except.pure] using success.symm
                  · simp [term, large, kindAt, member, failure, bind, Except.bind] at success
              rcases same with ⟨rfl, rfl⟩
              exact .variable kindAt
            | lower label | quoted label =>
              have head : atomic token.kind = some label := by simp [atomic, kindAt]
              by_cases opening : isChar '(' rest = true
              · obtain ⟨openToken, tail, rfl, openAt⟩ := isChar_exact opening
                cases argsAt : arguments fuel (depth + 1) scope endOffset tail with
                | error error =>
                  simp [term, large, kindAt, atomic, opening, argsAt,
                    bind, Except.bind] at success
                | ok result =>
                  rcases result with ⟨args, afterArgs⟩
                  cases closeAt : expect ')' endOffset afterArgs with
                  | error error =>
                    simp [term, large, kindAt, atomic, opening, argsAt, closeAt,
                      bind, Except.bind] at success
                  | ok result =>
                    rcases result with ⟨closeToken, afterClose⟩
                    obtain ⟨rfl, closing⟩ := expect_exact closeAt
                    simp [term, large, kindAt, atomic, opening, argsAt, closeAt,
                      bind, Except.bind, pure, Except.pure] at success
                    rcases success with ⟨rfl, rfl⟩
                    exact .application head openAt (ih.2 _ _ _ _ _ _ argsAt) closing
              · have notOpen : isChar '(' rest = false := Bool.eq_false_iff.mpr opening
                simp [term, large, kindAt, atomic, notOpen, pure, Except.pure] at success
                rcases success with ⟨rfl, rfl⟩
                exact .constant head notOpen
            | integer integer => simp [term, large, kindAt, failure] at success
            | truth | falsity | implies | equality positive | punctuation char =>
              simp [term, large, kindAt, atomic, failure] at success
          | reverse | nand | nor | iff | xor =>
            simp [term, large, kindAt, atomic, failure] at success
    · intro depth scope endOffset input values final success
      cases firstAt : term fuel depth scope endOffset input with
      | error error => simp [arguments, firstAt, bind, Except.bind] at success
      | ok result =>
        rcases result with ⟨first, rest⟩
        by_cases comma : isChar ',' rest = true
        · obtain ⟨commaToken, tail, rfl, commaAt⟩ := isChar_exact comma
          cases tailAt : arguments fuel depth scope endOffset tail with
          | error error =>
            simp [arguments, firstAt, comma, tailAt, bind, Except.bind] at success
          | ok result =>
            rcases result with ⟨more, afterMore⟩
            simp [arguments, firstAt, comma, tailAt, bind, Except.bind, pure, Except.pure] at success
            rcases success with ⟨rfl, rfl⟩
            exact .more (ih.1 _ _ _ _ _ _ firstAt) commaAt (ih.2 _ _ _ _ _ _ tailAt)
        · have notComma : isChar ',' rest = false := Bool.eq_false_iff.mpr comma
          simp [arguments, firstAt, notComma, bind, Except.bind, pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          exact .one (ih.1 _ _ _ _ _ _ firstAt) notComma

theorem term_sound {fuel depth scope endOffset input value rest}
    (success : term fuel depth scope endOffset input = .ok (value, rest)) :
    TermTokens input value rest := (term_arguments_sound fuel).1 _ _ _ _ _ _ success

theorem arguments_sound {fuel depth scope endOffset input values rest}
    (success : arguments fuel depth scope endOffset input = .ok (values, rest)) :
    ArgumentsTokens input values rest := (term_arguments_sound fuel).2 _ _ _ _ _ _ success

theorem atom_sound {fuel scope endOffset input value final}
    (success : atom fuel scope endOffset input = .ok (value, final)) :
    AtomTokens input value final := by
  cases headAt : term fuel 0 scope endOffset input with
  | error error => simp [atom, headAt, bind, Except.bind] at success
  | ok result =>
    rcases result with ⟨head, rest⟩
    have parsed := term_sound headAt
    cases rest with
    | nil =>
      cases head with
      | var label => simp [atom, headAt, failure, bind, Except.bind] at success
      | app label args =>
        simp [atom, headAt, bind, Except.bind, pure, Except.pure] at success
        rcases success with ⟨rfl, rfl⟩
        exact .predicate parsed (by simp [NoEquality])
    | cons operator middle =>
      simp only [atom, headAt, bind, Except.bind] at success
      split at success
      next positive kindAt =>
        cases rightAt : term fuel 0 scope endOffset middle with
        | error error => simp [rightAt] at success
        | ok result =>
          rcases result with ⟨right, rest⟩
          simp [rightAt, pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          exact .equality parsed kindAt (term_sound rightAt)
      next notEquality =>
        have noEquality : NoEquality (operator :: middle) := by
          intro token rest positive same
          cases same
          exact notEquality positive
        cases head with
        | var label => simp [failure] at success
        | app label args =>
          simp [pure, Except.pure] at success
          rcases success with ⟨rfl, rfl⟩
          exact .predicate parsed noEquality

#print axioms Fang.TptpCandidate.FullFof.expect_exact
#print axioms Fang.TptpCandidate.FullFof.isChar_exact
#print axioms Fang.TptpCandidate.FullFof.term_arguments_sound
#print axioms Fang.TptpCandidate.FullFof.term_sound
#print axioms Fang.TptpCandidate.FullFof.arguments_sound
#print axioms Fang.TptpCandidate.FullFof.atom_sound

end FullFof
end Fang.TptpCandidate
