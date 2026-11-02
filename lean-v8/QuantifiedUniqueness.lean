/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Extends the accepted FOF consuming-grammar uniqueness argument to binders. -/
import QuantifiedGrammar

namespace Fang.NamedQuantified.Grammar
open Source.Grammar (LowerName false_not_lower)
open FOFGrammar (truth_not_lower open_not_lower negate_not_lower)

theorem all_not_lower : ¬ LowerName "!" := by
  rintro ⟨first, rest, bytes, firstLower, _⟩
  change ([33] : Source.Grammar.Bytes) = first :: rest at bytes
  have same := (List.cons.inj bytes).1
  subst first
  simp [Source.Grammar.IsLower] at firstLower

theorem ex_not_lower : ¬ LowerName "?" := by
  rintro ⟨first, rest, bytes, firstLower, _⟩
  change ([63] : Source.Grammar.Bytes) = first :: rest at bytes
  have same := (List.cons.inj bytes).1
  subst first
  simp [Source.Grammar.IsLower] at firstLower

theorem FormulaTokens.unique_of_eq {input otherInput left right leftRest rightRest}
    (first : FormulaTokens input left leftRest) (competitor : FormulaTokens otherInput right rightRest)
    (sameInput : input = otherInput) : left = right ∧ leftRest = rightRest := by
  induction first generalizing otherInput right rightRest with
  | atom atom =>
    cases competitor with
    | atom other =>
      obtain ⟨same, rest⟩ := (sameInput ▸ atom).unique other
      obtain ⟨rfl, rfl⟩ := Source.Term.app.inj same
      exact ⟨rfl, rest⟩
    | truth => exact False.elim ((sameInput ▸ atom).app_not_head truth_not_lower rfl)
    | falsity => exact False.elim ((sameInput ▸ atom).app_not_head false_not_lower rfl)
    | neg => exact False.elim ((sameInput ▸ atom).app_not_head negate_not_lower rfl)
    | paren | conj | disj | implies => exact False.elim ((sameInput ▸ atom).app_not_head open_not_lower rfl)
    | all => exact False.elim ((sameInput ▸ atom).app_not_head all_not_lower rfl)
    | ex => exact False.elim ((sameInput ▸ atom).app_not_head ex_not_lower rfl)
  | truth rest =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head truth_not_lower rfl)
    | truth => exact ⟨rfl, (List.cons.inj sameInput).2⟩
    | falsity | neg | paren | conj | disj | implies | all | ex => simp at sameInput
  | falsity rest =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head false_not_lower rfl)
    | falsity => exact ⟨rfl, (List.cons.inj sameInput).2⟩
    | truth | neg | paren | conj | disj | implies | all | ex => simp at sameInput
  | neg child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head negate_not_lower rfl)
    | neg other =>
      obtain ⟨same, rest⟩ := ih other (List.cons.inj sameInput).2
      exact ⟨congrArg Formula.neg same, rest⟩
    | truth | falsity | paren | conj | disj | implies | all | ex => simp at sameInput
  | paren child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head open_not_lower rfl)
    | truth | falsity | neg | all | ex => simp at sameInput
    | paren other =>
      obtain ⟨same, rest⟩ := ih other (List.cons.inj sameInput).2
      exact ⟨same, (List.cons.inj rest).2⟩
    | conj other _ | disj other _ | implies other _ =>
      have impossible := (ih other (List.cons.inj sameInput).2).2
      simp at impossible
  | conj first second ihl ihr =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head open_not_lower rfl)
    | truth | falsity | neg | all | ex => simp at sameInput
    | paren other | disj other _ | implies other _ =>
      have impossible := (ihl other (List.cons.inj sameInput).2).2
      simp at impossible
    | conj other otherTail =>
      obtain ⟨same, middle⟩ := ihl other (List.cons.inj sameInput).2
      have middle := (List.cons.inj middle).2
      subst middle
      obtain ⟨tailSame, rest⟩ := ihr otherTail rfl
      cases same; cases tailSame
      exact ⟨rfl, (List.cons.inj rest).2⟩
  | disj first second ihl ihr =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head open_not_lower rfl)
    | truth | falsity | neg | all | ex => simp at sameInput
    | paren other | conj other _ | implies other _ =>
      have impossible := (ihl other (List.cons.inj sameInput).2).2
      simp at impossible
    | disj other otherTail =>
      obtain ⟨same, middle⟩ := ihl other (List.cons.inj sameInput).2
      have middle := (List.cons.inj middle).2
      subst middle
      obtain ⟨tailSame, rest⟩ := ihr otherTail rfl
      cases same; cases tailSame
      exact ⟨rfl, (List.cons.inj rest).2⟩
  | implies first second ihl ihr =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head open_not_lower rfl)
    | truth | falsity | neg | all | ex => simp at sameInput
    | paren other | conj other _ | disj other _ =>
      have impossible := (ihl other (List.cons.inj sameInput).2).2
      simp at impossible
    | implies other otherTail =>
      obtain ⟨same, middle⟩ := ihl other (List.cons.inj sameInput).2
      have middle := (List.cons.inj middle).2
      subst middle
      obtain ⟨tailSame, rest⟩ := ihr otherTail rfl
      cases same; cases tailSame
      exact ⟨rfl, (List.cons.inj rest).2⟩
  | all binders child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head all_not_lower rfl)
    | truth | falsity | neg | paren | conj | disj | implies | ex => simp at sameInput
    | all otherBinders otherChild =>
      have binderInput := (List.cons.inj (List.cons.inj sameInput).2).2
      obtain ⟨sameNames, sameBodyInput⟩ := (binderInput ▸ binders).unique otherBinders
      have bodyInput := (List.cons.inj sameBodyInput).2
      obtain ⟨sameBody, sameRest⟩ := ih otherChild bodyInput
      cases sameNames; cases sameBody
      exact ⟨rfl, sameRest⟩
  | ex binders child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head ex_not_lower rfl)
    | truth | falsity | neg | paren | conj | disj | implies | all => simp at sameInput
    | ex otherBinders otherChild =>
      have binderInput := (List.cons.inj (List.cons.inj sameInput).2).2
      obtain ⟨sameNames, sameBodyInput⟩ := (binderInput ▸ binders).unique otherBinders
      have bodyInput := (List.cons.inj sameBodyInput).2
      obtain ⟨sameBody, sameRest⟩ := ih otherChild bodyInput
      cases sameNames; cases sameBody
      exact ⟨rfl, sameRest⟩

theorem FormulaTokens.unique {input left right leftRest rightRest}
    (first : FormulaTokens input left leftRest) (second : FormulaTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := first.unique_of_eq second rfl

private theorem cnf_head {input clause rest}
    (parsed : FOFGrammar.CNFDeclarationTokens input clause rest) : input.head? = some "cnf" := by
  cases parsed
  rfl

theorem DeclarationTokens.unique {input left right leftRest rightRest}
    (first : DeclarationTokens input left leftRest) (second : DeclarationTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | cnf parsed =>
    cases second with
    | cnf other =>
      obtain ⟨same, rest⟩ := parsed.unique other
      exact ⟨congrArg Declaration.cnf same, rest⟩
    | fof valid parsedFof closed =>
      have impossible := cnf_head parsed
      simp at impossible
  | fof valid parsed closed =>
    cases second with
    | cnf other =>
      have impossible := cnf_head other
      simp at impossible
    | fof otherValid otherParsed otherClosed =>
      obtain ⟨same, rest⟩ := parsed.unique otherParsed
      cases same
      exact ⟨rfl, (List.cons.inj (List.cons.inj rest).2).2⟩

theorem DeclarationTokens.nonempty {input value rest} (parsed : DeclarationTokens input value rest) :
    input ≠ [] := by
  cases parsed with
  | cnf parsed => cases parsed; simp
  | fof => simp

theorem DeclarationsTokens.unique {input left right}
    (first : DeclarationsTokens input left) (second : DeclarationsTokens input right) : left = right := by
  induction first generalizing right with
  | nil =>
    cases second with
    | nil => rfl
    | cons head tail => exact False.elim (head.nonempty rfl)
  | cons head tail ih =>
    cases second with
    | nil => exact False.elim (head.nonempty rfl)
    | cons other otherTail =>
      obtain ⟨rfl, rfl⟩ := head.unique other
      exact congrArg (List.cons _) (ih otherTail)

theorem ParsesTokens.unique {input left right} (first : ParsesTokens input left)
    (second : ParsesTokens input right) : left = right := first.1.unique second.1

end Fang.NamedQuantified.Grammar
