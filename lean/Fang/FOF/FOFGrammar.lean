/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.NamedSource
import Fang.SourceLexing

namespace Fang.FOFGrammar
open Source.Grammar

/- Token spellings are consumed without a second executable parser. Identifier
   predicates refer to the independent source-byte grammar. Variables are
   present here because mixed CNF uses them; FOF declarations require Ground. -/
mutual
inductive TermTokens : List String → Source.Term → List String → Prop where
  | variableTerm (name : String) (rest : List String) (valid : VariableName name) :
      TermTokens (name :: rest) (.var name) rest
  | constant (name : String) (rest : List String) (valid : LowerName name)
      (noArguments : rest.head? ≠ some "(") :
      TermTokens (name :: rest) (.app name []) rest
  | application (name : String) {input rest arguments} (valid : LowerName name)
      (children : ArgumentsTokens input arguments rest) :
      TermTokens (name :: "(" :: input) (.app name arguments) rest
inductive ArgumentsTokens : List String → List Source.Term → List String → Prop where
  | last {input rest term} (head : TermTokens input term (")" :: rest)) :
      ArgumentsTokens input [term] rest
  | more {input middle rest term terms} (head : TermTokens input term ("," :: middle))
      (tail : ArgumentsTokens middle terms rest) : ArgumentsTokens input (term :: terms) rest
end

inductive TermsPrefix : List String → List Source.Term → List String → Prop where
  | last {input rest term} (head : TermTokens input term rest)
      (noComma : rest.head? ≠ some ",") : TermsPrefix input [term] rest
  | more {input middle rest term terms} (head : TermTokens input term ("," :: middle))
      (tail : TermsPrefix middle terms rest) : TermsPrefix input (term :: terms) rest

theorem TermsPrefix.arguments {input terms rest}
    (parsed : TermsPrefix input terms (")" :: rest)) : ArgumentsTokens input terms rest := by
  generalize ending : ")" :: rest = output at parsed
  induction parsed with
  | last head noComma => exact .last (ending ▸ head)
  | more head tail ih => exact .more head (ih ending)

inductive FormulaTokens : List String → NamedFOF.Formula → List String → Prop where
  | atom {input rest name arguments} (atom : TermTokens input (.app name arguments) rest) :
      FormulaTokens input (.atom name arguments) rest
  | truth (rest) : FormulaTokens ("$true" :: rest) .truth rest
  | falsity (rest) : FormulaTokens ("$false" :: rest) .falsity rest
  | neg {input rest body} (child : FormulaTokens input body rest) :
      FormulaTokens ("~" :: input) (.neg body) rest
  | paren {input rest body} (child : FormulaTokens input body (")" :: rest)) :
      FormulaTokens ("(" :: input) body rest
  | conj {input middle rest left right}
      (first : FormulaTokens input left ("&" :: middle))
      (second : FormulaTokens middle right (")" :: rest)) :
      FormulaTokens ("(" :: input) (.conj left right) rest
  | disj {input middle rest left right}
      (first : FormulaTokens input left ("|" :: middle))
      (second : FormulaTokens middle right (")" :: rest)) :
      FormulaTokens ("(" :: input) (.disj left right) rest
  | implies {input middle rest left right}
      (first : FormulaTokens input left ("=>" :: middle))
      (second : FormulaTokens middle right (")" :: rest)) :
      FormulaTokens ("(" :: input) (.implies left right) rest

inductive GroundDeclarationTokens : List String → String → NamedFOF.Formula → List String → Prop where
  | axiom {name input rest formula} (valid : LowerName name)
      (body : FormulaTokens input formula (")" :: "." :: rest))
      (ground : formula.Ground) :
      GroundDeclarationTokens ("fof" :: "(" :: name :: "," :: "axiom" :: "," :: input)
        name formula rest

mutual
theorem TermTokens.suffix {input term rest} (parsed : TermTokens input term rest) :
    ∃ front, front ≠ [] ∧ input = front ++ rest := by
  cases parsed with
  | variableTerm name rest valid => exact ⟨[name], by simp, rfl⟩
  | constant name rest valid noArguments => exact ⟨[name], by simp, rfl⟩
  | application name valid children =>
      obtain ⟨front, _, shape⟩ := children.suffix
      exact ⟨name :: "(" :: front, by simp, by simp [shape]⟩
theorem ArgumentsTokens.suffix {input terms rest} (parsed : ArgumentsTokens input terms rest) :
    ∃ front, front ≠ [] ∧ input = front ++ rest := by
  cases parsed with
  | last head =>
      obtain ⟨front, _, shape⟩ := head.suffix
      exact ⟨front ++ [")"], by simp, by simpa [List.append_assoc] using shape⟩
  | more head tail =>
      obtain ⟨front, _, shape⟩ := head.suffix
      obtain ⟨suffix, _, tailShape⟩ := tail.suffix
      exact ⟨front ++ "," :: suffix, by simp, by simp [shape, tailShape, List.append_assoc]⟩
end

theorem FormulaTokens.suffix {input formula rest} (parsed : FormulaTokens input formula rest) :
    ∃ front, front ≠ [] ∧ input = front ++ rest := by
  induction parsed with
  | atom atom => exact atom.suffix
  | truth rest => exact ⟨["$true"], by simp, rfl⟩
  | falsity rest => exact ⟨["$false"], by simp, rfl⟩
  | neg child ih =>
      obtain ⟨front, _, shape⟩ := ih
      exact ⟨"~" :: front, by simp, by simp [shape]⟩
  | paren child ih =>
      obtain ⟨front, _, shape⟩ := ih
      exact ⟨"(" :: front ++ [")"], by simp, by simp [shape, List.append_assoc]⟩
  | conj first second ih₁ ih₂ =>
      obtain ⟨front, _, shape⟩ := ih₁
      obtain ⟨suffix, _, tailShape⟩ := ih₂
      exact ⟨"(" :: front ++ "&" :: suffix ++ [")"], by simp,
        by simp [shape, tailShape, List.append_assoc]⟩
  | disj first second ih₁ ih₂ =>
      obtain ⟨front, _, shape⟩ := ih₁
      obtain ⟨suffix, _, tailShape⟩ := ih₂
      exact ⟨"(" :: front ++ "|" :: suffix ++ [")"], by simp,
        by simp [shape, tailShape, List.append_assoc]⟩
  | implies first second ih₁ ih₂ =>
      obtain ⟨front, _, shape⟩ := ih₁
      obtain ⟨suffix, _, tailShape⟩ := ih₂
      exact ⟨"(" :: front ++ "=>" :: suffix ++ [")"], by simp,
        by simp [shape, tailShape, List.append_assoc]⟩

theorem FormulaTokens.consumes {input formula rest} (parsed : FormulaTokens input formula rest) :
    rest.length < input.length := by
  obtain ⟨front, nonempty, rfl⟩ := parsed.suffix
  have positive : 0 < front.length := List.length_pos_iff.mpr nonempty
  simp only [List.length_append]
  omega

end Fang.FOFGrammar
