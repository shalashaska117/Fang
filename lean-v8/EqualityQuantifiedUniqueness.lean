/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Exact named AST and residual-token uniqueness for quantified equality. -/
import EqualityQuantifiedGrammar
import EqualityGrammarUniqueness

namespace Fang.NamedQuantifiedEquality.Grammar
open Source.Grammar (LowerName VariableName)
open EqualitySource.Grammar (negate_not_name false_not_name)

def literalFormula (value : EqualitySource.Literal) : Formula :=
  let atom := match value.atom with
    | .predicate name arguments => Formula.atom (.predicate name arguments)
    | .equal left right => Formula.atom (.equal left right)
  if value.positive then atom else .neg atom

theorem AtomTokens.literal {input formula rest} (parsed : AtomTokens input formula rest) :
    ∃ value, EqualitySource.Grammar.LiteralTokens input value rest ∧ formula = literalFormula value := by
  cases parsed with
  | predicate head stop => exact ⟨_, .predicate head stop, rfl⟩
  | equal first second => exact ⟨_, .equal first second, rfl⟩
  | notEqual first second => exact ⟨_, .notEqual first second, rfl⟩

theorem AtomTokens.unique {input left right leftRest rightRest}
    (first : AtomTokens input left leftRest) (second : AtomTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  obtain ⟨leftValue, leftGrammar, leftSame⟩ := first.literal
  obtain ⟨rightValue, rightGrammar, rightSame⟩ := second.literal
  obtain ⟨rfl, rfl⟩ := leftGrammar.unique rightGrammar
  exact ⟨leftSame.trans rightSame.symm, rfl⟩

theorem AtomTokens.not_head {input formula rest text} (parsed : AtomTokens input formula rest)
    (invalid : ¬ LowerName text ∧ ¬ VariableName text) : input.head? ≠ some text := by
  cases parsed with
  | predicate head _ | equal head _ | notEqual head _ => exact head.not_head invalid

theorem BindersTokens.unique_of_eq {input otherInput left right leftRest rightRest}
    (first : BindersTokens input left leftRest) (second : BindersTokens otherInput right rightRest)
    (sameInput : input = otherInput) : left = right ∧ leftRest = rightRest := by
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

private theorem initial_not_name (name : String) (first : UInt8) (rest : Source.Grammar.Bytes)
    (bytes : Source.Grammar.spelling name = first :: rest)
    (lower : ¬ Source.Grammar.IsLower first) (upper : ¬ Source.Grammar.IsUpper first) :
    ¬ LowerName name ∧ ¬ VariableName name := by
  constructor
  · rintro ⟨other, tail, shape, valid, _⟩
    have same := (List.cons.inj (bytes.symm.trans shape)).1
    cases same
    exact lower valid
  · rintro ⟨other, tail, shape, valid, _⟩
    have same := (List.cons.inj (bytes.symm.trans shape)).1
    cases same
    exact upper valid

theorem truth_not_name : ¬ LowerName "$true" ∧ ¬ VariableName "$true" :=
  initial_not_name "$true" 36 [116, 114, 117, 101] rfl (by simp [Source.Grammar.IsLower]) (by simp [Source.Grammar.IsUpper])

theorem open_not_name : ¬ LowerName "(" ∧ ¬ VariableName "(" :=
  initial_not_name "(" 40 [] rfl (by simp [Source.Grammar.IsLower]) (by simp [Source.Grammar.IsUpper])

theorem all_not_name : ¬ LowerName "!" ∧ ¬ VariableName "!" :=
  initial_not_name "!" 33 [] rfl (by simp [Source.Grammar.IsLower]) (by simp [Source.Grammar.IsUpper])

theorem ex_not_name : ¬ LowerName "?" ∧ ¬ VariableName "?" :=
  initial_not_name "?" 63 [] rfl (by simp [Source.Grammar.IsLower]) (by simp [Source.Grammar.IsUpper])
theorem FormulaTokens.unique_of_eq {input otherInput left right leftRest rightRest}
    (first : FormulaTokens input left leftRest) (competitor : FormulaTokens otherInput right rightRest)
    (sameInput : input = otherInput) : left = right ∧ leftRest = rightRest := by
  induction first generalizing otherInput right rightRest with
  | atom atom =>
    cases competitor with
    | atom other =>
      exact (sameInput ▸ atom).unique other
    | truth => exact False.elim ((sameInput ▸ atom).not_head truth_not_name rfl)
    | falsity => exact False.elim ((sameInput ▸ atom).not_head false_not_name rfl)
    | neg => exact False.elim ((sameInput ▸ atom).not_head negate_not_name rfl)
    | paren | conj | disj | implies => exact False.elim ((sameInput ▸ atom).not_head open_not_name rfl)
    | all => exact False.elim ((sameInput ▸ atom).not_head all_not_name rfl)
    | ex => exact False.elim ((sameInput ▸ atom).not_head ex_not_name rfl)
  | truth rest =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head truth_not_name rfl)
    | truth => exact ⟨rfl, (List.cons.inj sameInput).2⟩
    | falsity | neg | paren | conj | disj | implies | all | ex => simp at sameInput
  | falsity rest =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head false_not_name rfl)
    | falsity => exact ⟨rfl, (List.cons.inj sameInput).2⟩
    | truth | neg | paren | conj | disj | implies | all | ex => simp at sameInput
  | neg child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head negate_not_name rfl)
    | neg other =>
      obtain ⟨same, rest⟩ := ih other (List.cons.inj sameInput).2
      exact ⟨congrArg Formula.neg same, rest⟩
    | truth | falsity | paren | conj | disj | implies | all | ex => simp at sameInput
  | paren child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head open_not_name rfl)
    | truth | falsity | neg | all | ex => simp at sameInput
    | paren other =>
      obtain ⟨same, rest⟩ := ih other (List.cons.inj sameInput).2
      exact ⟨same, (List.cons.inj rest).2⟩
    | conj other _ | disj other _ | implies other _ =>
      have impossible := (ih other (List.cons.inj sameInput).2).2
      simp at impossible
  | conj first second ihl ihr =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head open_not_name rfl)
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
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head open_not_name rfl)
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
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head open_not_name rfl)
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
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head all_not_name rfl)
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
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head ex_not_name rfl)
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
    (parsed : EqualitySource.Grammar.StatementTokens input clause rest) : input.head? = some "cnf" := by
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

end Fang.NamedQuantifiedEquality.Grammar
