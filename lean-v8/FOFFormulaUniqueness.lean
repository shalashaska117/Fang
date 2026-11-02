/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import FOFCNFUniqueness
import FOFProblemGrammar

namespace Fang.FOFGrammar
open Source.Grammar (LowerName false_not_lower)

theorem truth_not_lower : ¬ LowerName "$true" := by
  rintro ⟨first, rest, bytes, firstLower, _⟩
  change ([36, 116, 114, 117, 101] : Source.Grammar.Bytes) = first :: rest at bytes
  have equal := (List.cons.inj bytes).1
  subst first
  simp [Source.Grammar.IsLower] at firstLower

theorem open_not_lower : ¬ LowerName "(" := by
  rintro ⟨first, rest, bytes, firstLower, _⟩
  change ([40] : Source.Grammar.Bytes) = first :: rest at bytes
  have equal := (List.cons.inj bytes).1
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
  | truth rest =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head truth_not_lower rfl)
    | truth => exact ⟨rfl, (List.cons.inj sameInput).2⟩
    | falsity | neg | paren | conj | disj | implies => simp at sameInput
  | falsity rest =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head false_not_lower rfl)
    | falsity => exact ⟨rfl, (List.cons.inj sameInput).2⟩
    | truth | neg | paren | conj | disj | implies => simp at sameInput
  | neg child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head negate_not_lower rfl)
    | neg other =>
      obtain ⟨same, rest⟩ := ih other (List.cons.inj sameInput).2
      exact ⟨congrArg NamedFOF.Formula.neg same, rest⟩
    | truth | falsity | paren | conj | disj | implies => simp at sameInput
  | paren child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head open_not_lower rfl)
    | truth | falsity | neg => simp at sameInput
    | paren other =>
      obtain ⟨same, rest⟩ := ih other (List.cons.inj sameInput).2
      exact ⟨same, (List.cons.inj rest).2⟩
    | conj other _ | disj other _ | implies other _ =>
      have impossible := (ih other (List.cons.inj sameInput).2).2
      simp at impossible
  | conj first second ih₁ ih₂ =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head open_not_lower rfl)
    | truth | falsity | neg => simp at sameInput
    | paren other | disj other _ | implies other _ =>
      have impossible := (ih₁ other (List.cons.inj sameInput).2).2
      simp at impossible
    | conj other otherTail =>
      obtain ⟨same, middle⟩ := ih₁ other (List.cons.inj sameInput).2
      have middle := (List.cons.inj middle).2
      subst middle
      obtain ⟨tailSame, rest⟩ := ih₂ otherTail rfl
      cases same; cases tailSame
      exact ⟨rfl, (List.cons.inj rest).2⟩
  | disj first second ih₁ ih₂ =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head open_not_lower rfl)
    | truth | falsity | neg => simp at sameInput
    | paren other | conj other _ | implies other _ =>
      have impossible := (ih₁ other (List.cons.inj sameInput).2).2
      simp at impossible
    | disj other otherTail =>
      obtain ⟨same, middle⟩ := ih₁ other (List.cons.inj sameInput).2
      have middle := (List.cons.inj middle).2
      subst middle
      obtain ⟨tailSame, rest⟩ := ih₂ otherTail rfl
      cases same; cases tailSame
      exact ⟨rfl, (List.cons.inj rest).2⟩
  | implies first second ih₁ ih₂ =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).app_not_head open_not_lower rfl)
    | truth | falsity | neg => simp at sameInput
    | paren other | conj other _ | disj other _ =>
      have impossible := (ih₁ other (List.cons.inj sameInput).2).2
      simp at impossible
    | implies other otherTail =>
      obtain ⟨same, middle⟩ := ih₁ other (List.cons.inj sameInput).2
      have middle := (List.cons.inj middle).2
      subst middle
      obtain ⟨tailSame, rest⟩ := ih₂ otherTail rfl
      cases same; cases tailSame
      exact ⟨rfl, (List.cons.inj rest).2⟩

theorem FormulaTokens.unique {input left right leftRest rightRest}
    (first : FormulaTokens input left leftRest) (second : FormulaTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := first.unique_of_eq second rfl

theorem GroundDeclarationTokens.unique {input leftName rightName left right leftRest rightRest}
    (first : GroundDeclarationTokens input leftName left leftRest)
    (second : GroundDeclarationTokens input rightName right rightRest) :
    leftName = rightName ∧ left = right ∧ leftRest = rightRest := by
  cases first with
  | «axiom» valid body ground =>
    cases second with
    | «axiom» otherValid otherBody otherGround =>
      obtain ⟨same, rest⟩ := body.unique otherBody
      exact ⟨rfl, same, (List.cons.inj (List.cons.inj rest).2).2⟩

theorem DeclarationTokens.unique {input left right leftRest rightRest}
    (first : DeclarationTokens input left leftRest) (second : DeclarationTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | cnf parsed =>
    cases second with
    | cnf other =>
      obtain ⟨same, rest⟩ := parsed.unique other
      exact ⟨congrArg NamedFOF.Declaration.cnf same, rest⟩
    | fof other =>
      have cnfHead : input.head? = some "cnf" := by cases parsed; rfl
      have fofHead : input.head? = some "fof" := by cases other; rfl
      rw [cnfHead] at fofHead
      simp at fofHead
  | fof parsed =>
    cases second with
    | cnf other =>
      have fofHead : input.head? = some "fof" := by cases parsed; rfl
      have cnfHead : input.head? = some "cnf" := by cases other; rfl
      rw [fofHead] at cnfHead
      simp at cnfHead
    | fof other =>
      obtain ⟨rfl, rfl, rest⟩ := parsed.unique other
      exact ⟨rfl, rest⟩

theorem DeclarationTokens.nonempty {input value rest} (parsed : DeclarationTokens input value rest) :
    input ≠ [] := by
  cases parsed with
  | cnf parsed => cases parsed; simp
  | fof parsed => cases parsed; simp

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

end Fang.FOFGrammar
