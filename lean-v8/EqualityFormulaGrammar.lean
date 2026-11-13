/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The token grammar of exported quantified equality formulas: the version-7
   formula grammar with TPTP atomic words as names. A lower word names itself
   and a single-quoted atom names its content. Binders keep the version-7
   relation. -/
import EqualityQuantifiedUniqueness
import Product.NameSpelling

namespace Fang.QuantifiedEqualityTstp.FormulaGrammar
open NamedQuantifiedEquality Source.Grammar TstpText

mutual
inductive TermTokens : List String → Source.Term → List String → Prop where
  | variableTerm (name : String) (rest : List String) (valid : VariableName name) :
      TermTokens (name :: rest) (.var name) rest
  | constant {word name : String} (rest : List String) (valid : AtomicText word name)
      (noArguments : rest.head? ≠ some "(") :
      TermTokens (word :: rest) (.app name []) rest
  | application {word name : String} {input rest arguments} (valid : AtomicText word name)
      (children : ArgumentsTokens input arguments rest) :
      TermTokens (word :: "(" :: input) (.app name arguments) rest
inductive ArgumentsTokens : List String → List Source.Term → List String → Prop where
  | last {input rest term} (head : TermTokens input term (")" :: rest)) :
      ArgumentsTokens input [term] rest
  | more {input middle rest term terms} (head : TermTokens input term ("," :: middle))
      (tail : ArgumentsTokens middle terms rest) : ArgumentsTokens input (term :: terms) rest
end

mutual
theorem TermTokens.unique {input left right leftRest rightRest}
    (first : TermTokens input left leftRest) (second : TermTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | variableTerm name rest valid =>
    cases second with
    | variableTerm => exact ⟨rfl, rfl⟩
    | constant _ word _ => exact False.elim (word.not_variable valid)
    | application word _ => exact False.elim (word.not_variable valid)
  | constant rest word noArguments =>
    cases second with
    | variableTerm _ _ upper => exact False.elim (word.not_variable upper)
    | constant _ other _ => exact ⟨by rw [word.functional other], rfl⟩
    | application => exact False.elim (noArguments rfl)
  | application word children =>
    cases second with
    | variableTerm _ _ upper => exact False.elim (word.not_variable upper)
    | constant _ _ noArguments => exact False.elim (noArguments rfl)
    | application other otherChildren =>
      obtain ⟨termsEqual, restEqual⟩ := children.unique otherChildren
      rw [word.functional other, termsEqual]
      exact ⟨rfl, restEqual⟩

theorem ArgumentsTokens.unique {input left right leftRest rightRest}
    (first : ArgumentsTokens input left leftRest)
    (second : ArgumentsTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | last head =>
    cases second with
    | last other =>
      obtain ⟨termEqual, restEqual⟩ := head.unique other
      exact ⟨congrArg (fun term => [term]) termEqual, (List.cons.inj restEqual).2⟩
    | more other tail =>
      have impossible := (head.unique other).2
      simp at impossible
  | more head tail =>
    cases second with
    | last other =>
      have impossible := (head.unique other).2
      simp at impossible
    | more other otherTail =>
      obtain ⟨termEqual, middleEqual⟩ := head.unique other
      have middleEqual := (List.cons.inj middleEqual).2
      subst middleEqual
      obtain ⟨termsEqual, restEqual⟩ := tail.unique otherTail
      cases termEqual; cases termsEqual
      exact ⟨rfl, restEqual⟩
end

/-- The first token of a term: a variable or an atomic word. -/
def NameHead (word : String) : Prop := VariableName word ∨ ∃ name, AtomicText word name

theorem TermTokens.head {input term rest} (parsed : TermTokens input term rest) :
    ∃ word tail, input = word :: tail ∧ NameHead word := by
  cases parsed with
  | variableTerm name rest valid => exact ⟨name, rest, rfl, Or.inl valid⟩
  | constant rest valid _ => exact ⟨_, rest, rfl, Or.inr ⟨_, valid⟩⟩
  | application valid _ => exact ⟨_, _, rfl, Or.inr ⟨_, valid⟩⟩

theorem not_name_head {word : String} {byte : UInt8} {bytes : Bytes}
    (spelled : spelling word = byte :: bytes) (lower : ¬ IsLower byte) (upper : ¬ IsUpper byte)
    (notQuote : byte ≠ 39) : ¬ NameHead word := by
  rintro (upperWord | ⟨name, atomic⟩)
  · obtain ⟨first, rest, shape, head, _⟩ := upperWord
    have same := (List.cons.inj (spelled.symm.trans shape)).1
    subst same
    exact upper head
  · obtain ⟨first, rest, shape, kind⟩ := atomic.first
    have same := (List.cons.inj (spelled.symm.trans shape)).1
    subst same
    rcases kind with letter | quote
    · exact lower letter
    · exact notQuote quote

theorem truth_not_head : ¬ NameHead "$true" :=
  not_name_head (byte := 36) (bytes := [116, 114, 117, 101]) rfl (by simp [IsLower]) (by simp [IsUpper]) (by decide)
theorem falsity_not_head : ¬ NameHead "$false" :=
  not_name_head (byte := 36) (bytes := [102, 97, 108, 115, 101]) rfl (by simp [IsLower]) (by simp [IsUpper])
    (by decide)
theorem negate_not_head : ¬ NameHead "~" :=
  not_name_head (byte := 126) (bytes := []) rfl (by simp [IsLower]) (by simp [IsUpper]) (by decide)
theorem open_not_head : ¬ NameHead "(" :=
  not_name_head (byte := 40) (bytes := []) rfl (by simp [IsLower]) (by simp [IsUpper]) (by decide)
theorem all_not_head : ¬ NameHead "!" :=
  not_name_head (byte := 33) (bytes := []) rfl (by simp [IsLower]) (by simp [IsUpper]) (by decide)
theorem ex_not_head : ¬ NameHead "?" :=
  not_name_head (byte := 63) (bytes := []) rfl (by simp [IsLower]) (by simp [IsUpper]) (by decide)

inductive AtomTokens : List String → Formula → List String → Prop where
  | predicate {input rest name arguments}
      (head : TermTokens input (.app name arguments) rest) (stop : EqualitySource.Grammar.PredicateEnd rest) :
      AtomTokens input (.atom (.predicate name arguments)) rest
  | equal {input middle rest left right}
      (first : TermTokens input left ("=" :: middle)) (second : TermTokens middle right rest) :
      AtomTokens input (.atom (.equal left right)) rest
  | notEqual {input middle rest left right}
      (first : TermTokens input left ("!=" :: middle)) (second : TermTokens middle right rest) :
      AtomTokens input (.neg (.atom (.equal left right))) rest

theorem AtomTokens.unique {input left right leftRest rightRest}
    (first : AtomTokens input left leftRest) (second : AtomTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | predicate head stop =>
    cases second with
    | predicate other _ =>
      obtain ⟨same, rest⟩ := head.unique other
      cases same
      exact ⟨rfl, rest⟩
    | equal other _ =>
      have rest := (head.unique other).2
      subst rest
      exact False.elim (stop.1 rfl)
    | notEqual other _ =>
      have rest := (head.unique other).2
      subst rest
      exact False.elim (stop.2 rfl)
  | equal one two =>
    cases second with
    | predicate other otherStop =>
      have rest := (other.unique one).2
      subst rest
      exact False.elim (otherStop.1 rfl)
    | equal other otherTwo =>
      obtain ⟨sameLeft, middle⟩ := one.unique other
      have middle := (List.cons.inj middle).2
      subst middle
      obtain ⟨sameRight, rest⟩ := two.unique otherTwo
      subst sameLeft
      subst sameRight
      exact ⟨rfl, rest⟩
    | notEqual other _ =>
      have impossible := (one.unique other).2
      simp at impossible
  | notEqual one two =>
    cases second with
    | predicate other otherStop =>
      have rest := (other.unique one).2
      subst rest
      exact False.elim (otherStop.2 rfl)
    | equal other _ =>
      have impossible := (one.unique other).2
      simp at impossible
    | notEqual other otherTwo =>
      obtain ⟨sameLeft, middle⟩ := one.unique other
      have middle := (List.cons.inj middle).2
      subst middle
      obtain ⟨sameRight, rest⟩ := two.unique otherTwo
      subst sameLeft
      subst sameRight
      exact ⟨rfl, rest⟩

theorem AtomTokens.not_head {input formula rest text} (parsed : AtomTokens input formula rest)
    (invalid : ¬ NameHead text) : input.head? ≠ some text := by
  intro atHead
  have first : ∃ word tail, input = word :: tail ∧ NameHead word := by
    cases parsed with
    | predicate head _ => exact head.head
    | equal head _ => exact head.head
    | notEqual head _ => exact head.head
  obtain ⟨word, tail, shape, valid⟩ := first
  subst shape
  simp only [List.head?_cons, Option.some.injEq] at atHead
  subst atHead
  exact invalid valid

inductive FormulaTokens : List String → Formula → List String → Prop where
  | atom {input value rest} (parsed : AtomTokens input value rest) : FormulaTokens input value rest
  | truth (rest) : FormulaTokens ("$true" :: rest) .truth rest
  | falsity (rest) : FormulaTokens ("$false" :: rest) .falsity rest
  | neg {input rest body} (child : FormulaTokens input body rest) :
      FormulaTokens ("~" :: input) (.neg body) rest
  | paren {input rest body} (child : FormulaTokens input body (")" :: rest)) :
      FormulaTokens ("(" :: input) body rest
  | conj {input middle rest left right} (first : FormulaTokens input left ("&" :: middle))
      (second : FormulaTokens middle right (")" :: rest)) :
      FormulaTokens ("(" :: input) (.conj left right) rest
  | disj {input middle rest left right} (first : FormulaTokens input left ("|" :: middle))
      (second : FormulaTokens middle right (")" :: rest)) :
      FormulaTokens ("(" :: input) (.disj left right) rest
  | implies {input middle rest left right} (first : FormulaTokens input left ("=>" :: middle))
      (second : FormulaTokens middle right (")" :: rest)) :
      FormulaTokens ("(" :: input) (.implies left right) rest
  | all {input bodyInput names body rest}
      (binders : NamedQuantifiedEquality.Grammar.BindersTokens input names (":" :: bodyInput))
      (child : FormulaTokens bodyInput body rest) :
      FormulaTokens ("!" :: "[" :: input) (body.bind true names) rest
  | ex {input bodyInput names body rest}
      (binders : NamedQuantifiedEquality.Grammar.BindersTokens input names (":" :: bodyInput))
      (child : FormulaTokens bodyInput body rest) :
      FormulaTokens ("?" :: "[" :: input) (body.bind false names) rest

theorem FormulaTokens.unique_of_eq {input otherInput left right leftRest rightRest}
    (first : FormulaTokens input left leftRest) (competitor : FormulaTokens otherInput right rightRest)
    (sameInput : input = otherInput) : left = right ∧ leftRest = rightRest := by
  induction first generalizing otherInput right rightRest with
  | atom atom =>
    cases competitor with
    | atom other =>
      exact (sameInput ▸ atom).unique other
    | truth => exact False.elim ((sameInput ▸ atom).not_head truth_not_head rfl)
    | falsity => exact False.elim ((sameInput ▸ atom).not_head falsity_not_head rfl)
    | neg => exact False.elim ((sameInput ▸ atom).not_head negate_not_head rfl)
    | paren | conj | disj | implies => exact False.elim ((sameInput ▸ atom).not_head open_not_head rfl)
    | all => exact False.elim ((sameInput ▸ atom).not_head all_not_head rfl)
    | ex => exact False.elim ((sameInput ▸ atom).not_head ex_not_head rfl)
  | truth rest =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head truth_not_head rfl)
    | truth => exact ⟨rfl, (List.cons.inj sameInput).2⟩
    | falsity | neg | paren | conj | disj | implies | all | ex => simp at sameInput
  | falsity rest =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head falsity_not_head rfl)
    | falsity => exact ⟨rfl, (List.cons.inj sameInput).2⟩
    | truth | neg | paren | conj | disj | implies | all | ex => simp at sameInput
  | neg child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head negate_not_head rfl)
    | neg other =>
      obtain ⟨same, rest⟩ := ih other (List.cons.inj sameInput).2
      exact ⟨congrArg Formula.neg same, rest⟩
    | truth | falsity | paren | conj | disj | implies | all | ex => simp at sameInput
  | paren child ih =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head open_not_head rfl)
    | truth | falsity | neg | all | ex => simp at sameInput
    | paren other =>
      obtain ⟨same, rest⟩ := ih other (List.cons.inj sameInput).2
      exact ⟨same, (List.cons.inj rest).2⟩
    | conj other _ | disj other _ | implies other _ =>
      have impossible := (ih other (List.cons.inj sameInput).2).2
      simp at impossible
  | conj first second ihl ihr =>
    cases competitor with
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head open_not_head rfl)
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
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head open_not_head rfl)
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
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head open_not_head rfl)
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
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head all_not_head rfl)
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
    | atom other => exact False.elim ((sameInput.symm ▸ other).not_head ex_not_head rfl)
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

#print axioms Fang.QuantifiedEqualityTstp.FormulaGrammar.TermTokens.unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaGrammar.AtomTokens.unique
#print axioms Fang.QuantifiedEqualityTstp.FormulaGrammar.FormulaTokens.unique

end Fang.QuantifiedEqualityTstp.FormulaGrammar
