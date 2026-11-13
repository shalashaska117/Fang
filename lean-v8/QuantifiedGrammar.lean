/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Declarative nested-quantifier token grammar, separate from decoder code. -/
import QuantifiedProblem
import FOFFormulaUniqueness

namespace Fang.NamedQuantified

def Formula.bind (universal : Bool) (names : List String) (body : Formula) : Formula :=
  names.foldr (fun name tail => if universal then .all name tail else .ex name tail) body

namespace Grammar
open Source.Grammar (LowerName VariableName)

/-- A nonempty list consumes its closing bracket. Repeated names are retained. -/
inductive BindersTokens : List String → List String → List String → Prop where
  | last {name rest} (valid : VariableName name) :
      BindersTokens (name :: "]" :: rest) [name] rest
  | more {name input names rest} (valid : VariableName name)
      (tail : BindersTokens input names rest) :
      BindersTokens (name :: "," :: input) (name :: names) rest

theorem BindersTokens.nonempty {input names rest} (parsed : BindersTokens input names rest) :
    names ≠ [] := by cases parsed <;> simp

theorem BindersTokens.head_valid {input names rest} (parsed : BindersTokens input names rest) :
    ∃ name tail, input = name :: tail ∧ VariableName name := by
  cases parsed with
  | last valid => exact ⟨_, _, rfl, valid⟩
  | more valid tail => exact ⟨_, _, rfl, valid⟩

theorem BindersTokens.unique_of_eq {input otherInput left right leftRest rightRest}
    (first : BindersTokens input left leftRest) (second : BindersTokens otherInput right rightRest)
    (sameInput : input = otherInput) :
    left = right ∧ leftRest = rightRest := by
  induction first generalizing otherInput right rightRest with
  | last valid =>
    cases second with
    | last other =>
      have sameName := (List.cons.inj sameInput).1
      have sameRest := (List.cons.inj (List.cons.inj sameInput).2).2
      exact ⟨congrArg (fun name => [name]) sameName, sameRest⟩
    | more other tail =>
      have impossible := (List.cons.inj (List.cons.inj sameInput).2).1
      simp at impossible
  | more valid tail ih =>
    cases second with
    | last other =>
      have impossible := (List.cons.inj (List.cons.inj sameInput).2).1
      simp at impossible
    | more otherValid other =>
      have sameName := (List.cons.inj sameInput).1
      have sameTail := (List.cons.inj (List.cons.inj sameInput).2).2
      obtain ⟨sameNames, sameRest⟩ := ih other sameTail
      cases sameName; cases sameNames
      exact ⟨rfl, sameRest⟩

theorem BindersTokens.unique {input left right leftRest rightRest}
    (first : BindersTokens input left leftRest) (second : BindersTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := first.unique_of_eq second rfl

theorem BindersTokens.suffix {input names rest} (parsed : BindersTokens input names rest) :
    ∃ front, front ≠ [] ∧ input = front ++ rest := by
  induction parsed with
  | @last name rest valid => exact ⟨[name, "]"], by simp, rfl⟩
  | @more name input names rest valid tail ih =>
    obtain ⟨front, _, shape⟩ := ih
    exact ⟨name :: "," :: front, by simp, by simp [shape]⟩

inductive FormulaTokens : List String → Formula → List String → Prop where
  | atom {input rest name arguments}
      (atom : FOFGrammar.TermTokens input (.app name arguments) rest) :
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
  | all {input bodyInput names body rest}
      (binders : BindersTokens input names (":" :: bodyInput))
      (child : FormulaTokens bodyInput body rest) :
      FormulaTokens ("!" :: "[" :: input) (body.bind true names) rest
  | ex {input bodyInput names body rest}
      (binders : BindersTokens input names (":" :: bodyInput))
      (child : FormulaTokens bodyInput body rest) :
      FormulaTokens ("?" :: "[" :: input) (body.bind false names) rest

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
  | conj first second ihl ihr =>
    obtain ⟨front, _, shape⟩ := ihl
    obtain ⟨tail, _, tailShape⟩ := ihr
    exact ⟨"(" :: front ++ "&" :: tail ++ [")"], by simp,
      by simp [shape, tailShape, List.append_assoc]⟩
  | disj first second ihl ihr =>
    obtain ⟨front, _, shape⟩ := ihl
    obtain ⟨tail, _, tailShape⟩ := ihr
    exact ⟨"(" :: front ++ "|" :: tail ++ [")"], by simp,
      by simp [shape, tailShape, List.append_assoc]⟩
  | implies first second ihl ihr =>
    obtain ⟨front, _, shape⟩ := ihl
    obtain ⟨tail, _, tailShape⟩ := ihr
    exact ⟨"(" :: front ++ "=>" :: tail ++ [")"], by simp,
      by simp [shape, tailShape, List.append_assoc]⟩
  | all binders child ih =>
    obtain ⟨front, _, shape⟩ := binders.suffix
    obtain ⟨tail, _, tailShape⟩ := ih
    exact ⟨"!" :: "[" :: front ++ ":" :: tail, by simp,
      by simp [shape, tailShape, List.append_assoc]⟩
  | ex binders child ih =>
    obtain ⟨front, _, shape⟩ := binders.suffix
    obtain ⟨tail, _, tailShape⟩ := ih
    exact ⟨"?" :: "[" :: front ++ ":" :: tail, by simp,
      by simp [shape, tailShape, List.append_assoc]⟩

theorem FormulaTokens.consumes {input formula rest} (parsed : FormulaTokens input formula rest) :
    rest.length < input.length := by
  obtain ⟨front, nonempty, rfl⟩ := parsed.suffix
  have positive := List.length_pos_iff.mpr nonempty
  simp only [List.length_append]
  omega

inductive DeclarationTokens : List String → Declaration → List String → Prop where
  | cnf {input clause rest} (parsed : FOFGrammar.CNFDeclarationTokens input clause rest) :
      DeclarationTokens input (.cnf clause) rest
  | fof {name input rest formula} (valid : LowerName name)
      (parsed : FormulaTokens input formula (")" :: "." :: rest))
      (closed : formula.Within []) :
      DeclarationTokens ("fof" :: "(" :: name :: "," :: "axiom" :: "," :: input)
        (.fof name formula) rest

inductive DeclarationsTokens : List String → List Declaration → Prop where
  | nil : DeclarationsTokens [] []
  | cons {input middle first rest} (head : DeclarationTokens input first middle)
      (tail : DeclarationsTokens middle rest) : DeclarationsTokens input (first :: rest)

/-- Token grammar only. A byte lexer and executable decoder are still required. -/
def ParsesTokens (input : List String) (declarations : List Declaration) : Prop :=
  DeclarationsTokens input declarations ∧ (declarations.map Declaration.name).Nodup

end Grammar
end Fang.NamedQuantified
