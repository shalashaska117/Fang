/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import FofFormulaSound

namespace Fang.TptpCandidate.FullFof.Grammar

private def TermUnique (input : List Token) (left : Source.Term) (leftRest : List Token) : Prop :=
  ∀ {right rightRest}, TermTokens input right rightRest → left = right ∧ leftRest = rightRest

private def ArgumentsUnique (input : List Token) (left : List Source.Term) (leftRest : List Token) : Prop :=
  ∀ {right rightRest}, ArgumentsTokens input right rightRest → left = right ∧ leftRest = rightRest

private theorem unique_variable {token rest name} (leftAt : token.kind = .legacy (.variable name)) :
    TermUnique (token :: rest) (.var name) rest := by
  intro right rightRest second
  cases second <;> simp_all [atomic]

private theorem unique_constant {token rest name} (leftHead : atomic token.kind = some name)
    (noOpen : isChar '(' rest = false) : TermUnique (token :: rest) (.app name []) rest := by
  intro right rightRest second
  cases second with
  | «variable» rightAt => simp_all [atomic]
  | constant rightHead _ => simp_all
  | application _ openAt _ _ => simp_all [Punct, isChar]

private theorem unique_application {token opening input args closing rest name}
    (leftHead : atomic token.kind = some name) (openAt : Punct opening '(')
    (_leftArgs : ArgumentsTokens input args (closing :: rest)) (_closeAt : Punct closing ')')
    (ih : ArgumentsUnique input args (closing :: rest)) :
    TermUnique (token :: opening :: input) (.app name args) rest := by
  intro right rightRest second
  cases second with
  | «variable» rightAt => simp_all [atomic]
  | constant _ noOpen => simp_all [Punct, isChar]
  | application rightHead _ rightArgs _ =>
    obtain ⟨rfl, sameRest⟩ := ih rightArgs
    obtain ⟨rfl, rfl⟩ := List.cons.inj sameRest
    simp_all

private theorem unique_one {input first rest} (_parsed : TermTokens input first rest)
    (noComma : isChar ',' rest = false) (ih : TermUnique input first rest) :
    ArgumentsUnique input [first] rest := by
  intro right rightRest second
  cases second with
  | one parsed _ =>
    obtain ⟨rfl, rfl⟩ := ih parsed
    exact ⟨rfl, rfl⟩
  | more parsed commaAt _ =>
    have sameRest := (ih parsed).2
    simp [sameRest, isChar] at noComma
    exact False.elim (noComma commaAt)

private theorem unique_more {input first comma tail more rest}
    (_parsed : TermTokens input first (comma :: tail)) (commaAt : Punct comma ',')
    (_arguments : ArgumentsTokens tail more rest) (ihTerm : TermUnique input first (comma :: tail))
    (ihArgs : ArgumentsUnique tail more rest) : ArgumentsUnique input (first :: more) rest := by
  intro right rightRest second
  cases second with
  | one parsed noComma =>
    have sameRest := (ihTerm parsed).2
    simp [← sameRest, isChar] at noComma
    exact False.elim (noComma commaAt)
  | more parsed _ args =>
    obtain ⟨rfl, sameTail⟩ := ihTerm parsed
    obtain ⟨rfl, rfl⟩ := List.cons.inj sameTail
    obtain ⟨rfl, rfl⟩ := ihArgs args
    exact ⟨rfl, rfl⟩

theorem term_unique {input left leftRest right rightRest}
    (first : TermTokens input left leftRest) (second : TermTokens input right rightRest) :
    left = right ∧ leftRest = rightRest :=
  TermTokens.rec (motive_1 := fun input value rest _ => TermUnique input value rest)
    (motive_2 := fun input value rest _ => ArgumentsUnique input value rest)
    unique_variable unique_constant unique_application unique_one unique_more first second

theorem arguments_unique {input left leftRest right rightRest}
    (first : ArgumentsTokens input left leftRest) (second : ArgumentsTokens input right rightRest) :
    left = right ∧ leftRest = rightRest :=
  ArgumentsTokens.rec (motive_1 := fun input value rest _ => TermUnique input value rest)
    (motive_2 := fun input value rest _ => ArgumentsUnique input value rest)
    unique_variable unique_constant unique_application unique_one unique_more first second

theorem atom_unique {input left leftRest right rightRest}
    (first : AtomTokens input left leftRest) (second : AtomTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | predicate firstTerm noEquality =>
    cases second with
    | predicate secondTerm _ =>
      obtain ⟨same, rfl⟩ := term_unique firstTerm secondTerm
      cases same
      exact ⟨rfl, rfl⟩
    | equality secondTerm kind _ =>
      have rest := (term_unique firstTerm secondTerm).2
      exact False.elim (noEquality _ _ _ rest kind)
  | equality firstTerm kind firstRight =>
    cases second with
    | predicate secondTerm noEquality =>
      have rest := (term_unique firstTerm secondTerm).2
      exact False.elim (noEquality _ _ _ rest.symm kind)
    | equality secondTerm secondKind secondRight =>
      obtain ⟨rfl, rest⟩ := term_unique firstTerm secondTerm
      obtain ⟨rfl, rfl⟩ := List.cons.inj rest
      have positive := Kind.legacy.inj (kind.symm.trans secondKind)
      cases TptpCandidate.Kind.equality.inj positive
      obtain ⟨rfl, rfl⟩ := term_unique firstRight secondRight
      exact ⟨rfl, rfl⟩

theorem binders_unique {input left leftRest right rightRest}
    (first : BindersTokens input left leftRest) (second : BindersTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction first generalizing right rightRest with
  | one kind noComma notTyped =>
    cases second with
    | one secondKind _ _ => simp_all
    | more _ commaAt _ => simp_all [isChar, Punct]
  | more kind commaAt tail ih =>
    cases second with
    | one _ noComma _ => simp_all [isChar, Punct]
    | more secondKind _ secondTail =>
      obtain ⟨rfl, rfl⟩ := ih secondTail
      simp_all

#print axioms Fang.TptpCandidate.FullFof.Grammar.term_unique
#print axioms Fang.TptpCandidate.FullFof.Grammar.arguments_unique
#print axioms Fang.TptpCandidate.FullFof.Grammar.atom_unique
#print axioms Fang.TptpCandidate.FullFof.Grammar.binders_unique

end Fang.TptpCandidate.FullFof.Grammar
