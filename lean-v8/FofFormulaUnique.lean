/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import FofTermUnique

namespace Fang.TptpCandidate.FullFof.Grammar

def HeadValid (kind : Kind) : Prop :=
  (∃ name, kind = .legacy (.variable name)) ∨ (∃ name, atomic kind = some name)

theorem term_starts {input value rest} (parsed : TermTokens input value rest) :
    ∃ token tail, input = token :: tail ∧ HeadValid token.kind := by
  cases parsed with
  | «variable» kind => exact ⟨_, _, rfl, Or.inl ⟨_, kind⟩⟩
  | constant kind _ => exact ⟨_, _, rfl, Or.inr ⟨_, kind⟩⟩
  | application kind _ _ _ => exact ⟨_, _, rfl, Or.inr ⟨_, kind⟩⟩

theorem atom_starts {input value rest} (parsed : AtomTokens input value rest) :
    ∃ token tail, input = token :: tail ∧ HeadValid token.kind := by
  cases parsed with
  | predicate head _ => exact term_starts head
  | equality head _ _ => exact term_starts head

theorem atom_head_valid {token tail value rest} (parsed : AtomTokens (token :: tail) value rest) :
    HeadValid token.kind := by
  obtain ⟨_, _, shape, valid⟩ := atom_starts parsed
  cases shape
  exact valid

theorem quantifierKind_injective : Function.Injective quantifierKind := by
  intro left right same
  cases left <;> cases right <;> simp_all [quantifierKind]

theorem chain_operator_unique {input left output rest operator left' output' rest' operator'}
    (first : ChainTokens operator left input output rest)
    (second : ChainTokens operator' left' input output' rest') : operator = operator' := by
  cases first <;> cases second <;> simp_all

private def UnitUnique (input : List Token) (left : Formula) (leftRest : List Token) : Prop :=
  ∀ {right rightRest}, UnitTokens input right rightRest → left = right ∧ leftRest = rightRest

private def FormulaUnique (input : List Token) (left : Formula) (leftRest : List Token) : Prop :=
  ∀ {right rightRest}, FormulaTokens input right rightRest → left = right ∧ leftRest = rightRest

private def ChainUnique (operator : Binary) (left : Formula) (input : List Token)
    (output : Formula) (rest : List Token) : Prop :=
  ∀ {right rightRest}, ChainTokens operator left input right rightRest → output = right ∧ rest = rightRest

private theorem unique_truth {token rest} (kind : token.kind = .legacy .truth) :
    UnitUnique (token :: rest) .truth rest := by
  intro right rightRest second
  cases second <;> try simp_all [Punct, quantifierKind]
  rename_i parsed
  have valid := atom_head_valid parsed
  simp_all [HeadValid, atomic]

private theorem unique_falsity {token rest} (kind : token.kind = .legacy .falsity) :
    UnitUnique (token :: rest) .falsity rest := by
  intro right rightRest second
  cases second <;> try simp_all [Punct, quantifierKind]
  rename_i parsed
  have valid := atom_head_valid parsed
  simp_all [HeadValid, atomic]

private theorem unique_atom {input body rest} (first : AtomTokens input body rest) :
    UnitUnique input body rest := by
  intro right rightRest second
  obtain ⟨token, tail, rfl, valid⟩ := atom_starts first
  cases second <;> try simp_all [HeadValid, atomic, Punct, quantifierKind]
  exact atom_unique first ‹AtomTokens _ _ _›

private theorem unique_neg {token input body rest} (kind : Punct token '~')
    (_parsed : UnitTokens input body rest) (ih : UnitUnique input body rest) :
    UnitUnique (token :: input) (.neg body) rest := by
  intro right rightRest second
  cases second <;> try simp_all [Punct, quantifierKind]
  · rename_i parsed
    have valid := atom_head_valid parsed
    simp_all [HeadValid, atomic]
  · obtain ⟨rfl, rfl⟩ := ih ‹UnitTokens input _ _›
    exact ⟨rfl, rfl⟩
  · split at kind <;> contradiction

private theorem unique_group {opening input body closing rest} (openAt : Punct opening '(')
    (_parsed : FormulaTokens input body (closing :: rest)) (_closeAt : Punct closing ')')
    (ih : FormulaUnique input body (closing :: rest)) : UnitUnique (opening :: input) body rest := by
  intro right rightRest second
  cases second <;> try simp_all [Punct, quantifierKind]
  · rename_i parsed
    have valid := atom_head_valid parsed
    simp_all [HeadValid, atomic]
  · obtain ⟨rfl, sameRest⟩ := ih ‹FormulaTokens input _ _›
    obtain ⟨rfl, rfl⟩ := List.cons.inj sameRest
    exact ⟨rfl, rfl⟩
  · split at openAt <;> contradiction

private theorem unique_quantified {token opening input names closing colon middle body rest universal}
    (kind : token.kind = quantifierKind universal) (_openAt : Punct opening '[')
    (binders : BindersTokens input names (closing :: colon :: middle)) (_closeAt : Punct closing ']')
    (_colonAt : Punct colon ':') (_parsed : UnitTokens middle body rest)
    (ih : UnitUnique middle body rest) :
    UnitUnique (token :: opening :: input) (close universal names body) rest := by
  intro right rightRest second
  cases second <;> try simp_all [Punct, quantifierKind]
  · rename_i parsed
    have valid := atom_head_valid parsed
    simp_all [HeadValid, atomic]
  · cases universal <;> simp_all
  · cases universal <;> simp_all
  · rename_i names' closing' colon' middle' body' universal' closeAt' colonAt' kindAt' binders' parsed'
    have flags : universal = universal' := by cases universal <;> cases universal' <;> simp_all
    subst universal'
    obtain ⟨rfl, sameRest⟩ := binders_unique binders binders'
    have sameMiddle := (List.cons.inj (List.cons.inj sameRest).2).2
    rw [← sameMiddle] at parsed'
    obtain ⟨rfl, rfl⟩ := ih parsed'
    exact ⟨rfl, rfl⟩

private theorem unique_formula_one {input body rest} (_parsed : UnitTokens input body rest)
    (noOperator : nextBinary rest = none) (ih : UnitUnique input body rest) : FormulaUnique input body rest := by
  intro right rightRest second
  cases second with
  | one parsed _ => exact ih parsed
  | binary parsed chain =>
    obtain ⟨rfl, rfl⟩ := ih parsed
    cases chain <;> simp_all [nextBinary]

private theorem unique_formula_binary {input left middle body rest operator}
    (_parsed : UnitTokens input left middle) (tail : ChainTokens operator left middle body rest)
    (ihUnit : UnitUnique input left middle) (ihChain : ChainUnique operator left middle body rest) :
    FormulaUnique input body rest := by
  intro right rightRest second
  cases second with
  | one parsed noOperator =>
    obtain ⟨rfl, rfl⟩ := ihUnit parsed
    cases tail <;> simp_all [nextBinary]
  | binary parsed other =>
    obtain ⟨rfl, rfl⟩ := ihUnit parsed
    obtain rfl := chain_operator_unique tail other
    exact ihChain other

private theorem unique_chain_one {operator left token middle right rest}
    (_kind : binary token.kind = some operator) (_parsed : UnitTokens middle right rest)
    (finished : (operator.associative && nextBinary rest == some operator) = false)
    (ih : UnitUnique middle right rest) :
    ChainUnique operator left (token :: middle) (.pair operator left right) rest := by
  intro output final second
  cases second with
  | one _ parsed _ =>
    obtain ⟨rfl, rfl⟩ := ih parsed
    exact ⟨rfl, rfl⟩
  | more _ parsed associative following _ =>
    obtain ⟨rfl, rfl⟩ := ih parsed
    simp_all

private theorem unique_chain_more {operator left token middle right tail body rest}
    (_kind : binary token.kind = some operator) (_parsed : UnitTokens middle right tail)
    (associative : operator.associative = true) (following : nextBinary tail = some operator)
    (_remaining : ChainTokens operator (.pair operator left right) tail body rest)
    (ihUnit : UnitUnique middle right tail)
    (ihChain : ChainUnique operator (.pair operator left right) tail body rest) :
    ChainUnique operator left (token :: middle) body rest := by
  intro output final second
  cases second with
  | one _ parsed finished =>
    obtain ⟨rfl, rfl⟩ := ihUnit parsed
    simp_all
  | more _ parsed _ _ remaining =>
    obtain ⟨rfl, rfl⟩ := ihUnit parsed
    exact ihChain remaining

theorem unit_unique {input left leftRest right rightRest}
    (first : UnitTokens input left leftRest) (second : UnitTokens input right rightRest) :
    left = right ∧ leftRest = rightRest :=
  UnitTokens.rec (motive_1 := fun input value rest _ => UnitUnique input value rest)
    (motive_2 := fun input value rest _ => FormulaUnique input value rest)
    (motive_3 := fun operator left input value rest _ => ChainUnique operator left input value rest)
    unique_truth unique_falsity unique_atom unique_neg unique_group unique_quantified
    unique_formula_one unique_formula_binary unique_chain_one unique_chain_more first second

theorem formula_unique {input left leftRest right rightRest}
    (first : FormulaTokens input left leftRest) (second : FormulaTokens input right rightRest) :
    left = right ∧ leftRest = rightRest :=
  FormulaTokens.rec (motive_1 := fun input value rest _ => UnitUnique input value rest)
    (motive_2 := fun input value rest _ => FormulaUnique input value rest)
    (motive_3 := fun operator left input value rest _ => ChainUnique operator left input value rest)
    unique_truth unique_falsity unique_atom unique_neg unique_group unique_quantified
    unique_formula_one unique_formula_binary unique_chain_one unique_chain_more first second

theorem chain_unique {operator left input first firstRest second secondRest}
    (a : ChainTokens operator left input first firstRest) (b : ChainTokens operator left input second secondRest) :
    first = second ∧ firstRest = secondRest :=
  ChainTokens.rec (motive_1 := fun input value rest _ => UnitUnique input value rest)
    (motive_2 := fun input value rest _ => FormulaUnique input value rest)
    (motive_3 := fun operator left input value rest _ => ChainUnique operator left input value rest)
    unique_truth unique_falsity unique_atom unique_neg unique_group unique_quantified
    unique_formula_one unique_formula_binary unique_chain_one unique_chain_more a b

end Fang.TptpCandidate.FullFof.Grammar
