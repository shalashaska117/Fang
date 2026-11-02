/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import FofFormulaUnique
import FofScope

namespace Fang.TptpCandidate.FullFof.Grammar

theorem cnfLiteral_starts {input value rest} (parsed : CnfLiteralTokens input value rest) :
    ∃ token tail, input = token :: tail ∧ (HeadValid token.kind ∨ Punct token '~') := by
  cases parsed with
  | positive atom =>
    obtain ⟨token, tail, rfl, valid⟩ := atom_starts atom
    exact ⟨token, tail, rfl, Or.inl valid⟩
  | negative kind _ => exact ⟨_, _, rfl, Or.inr kind⟩

theorem cnfLiteral_unique {input left leftRest right rightRest}
    (first : CnfLiteralTokens input left leftRest) (second : CnfLiteralTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | positive parsed =>
    cases second with
    | positive other => exact atom_unique parsed other
    | negative kind _ =>
      have valid := atom_head_valid parsed
      simp_all [HeadValid, atomic, Punct]
  | negative kind parsed =>
    cases second with
    | positive other =>
      have valid := atom_head_valid other
      simp_all [HeadValid, atomic, Punct]
    | negative _ other =>
      obtain ⟨same, rfl⟩ := atom_unique parsed other
      exact ⟨congrArg Formula.neg same, rfl⟩

theorem cnfLiterals_unique {input left leftRest right rightRest}
    (first : CnfLiteralsTokens input left leftRest) (second : CnfLiteralsTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  induction first generalizing right rightRest with
  | one parsed noBar =>
    cases second with
    | one other _ =>
      obtain ⟨rfl, rfl⟩ := cnfLiteral_unique parsed other
      exact ⟨rfl, rfl⟩
    | more other bar _ =>
      have rest := (cnfLiteral_unique parsed other).2
      simp [rest, isChar] at noBar
      exact False.elim (noBar bar)
  | more parsed bar tail ih =>
    cases second with
    | one other noBar =>
      have rest := (cnfLiteral_unique parsed other).2
      simp [← rest, isChar] at noBar
      exact False.elim (noBar bar)
    | more other _ others =>
      obtain ⟨rfl, rest⟩ := cnfLiteral_unique parsed other
      obtain ⟨rfl, rfl⟩ := List.cons.inj rest
      obtain ⟨rfl, rfl⟩ := ih others
      exact ⟨rfl, rfl⟩

theorem cnfLiterals_head_valid {token input values rest}
    (parsed : CnfLiteralsTokens (token :: input) values rest) : HeadValid token.kind ∨ Punct token '~' := by
  cases parsed with
  | one first _ | more first _ _ =>
    obtain ⟨_, _, shape, valid⟩ := cnfLiteral_starts first
    cases shape
    exact valid

theorem body_unique {input left leftRest right rightRest} (kind : BodyKind left = BodyKind right)
    (first : BodyTokens input left leftRest) (second : BodyTokens input right rightRest) :
    left = right ∧ leftRest = rightRest := by
  cases first with
  | fof parsed =>
    cases second with
    | fof other =>
      obtain ⟨rfl, rfl⟩ := formula_unique parsed other
      exact ⟨rfl, rfl⟩
    | cnfFalse _ _ _ | cnf _ _ _ => simp [BodyKind] at kind
  | cnfFalse opening falsity closing =>
    cases second with
    | fof _ => simp [BodyKind] at kind
    | cnfFalse _ _ _ => exact ⟨rfl, rfl⟩
    | cnf _ parsed _ =>
      have valid := cnfLiterals_head_valid parsed
      simp_all [HeadValid, atomic, Punct]
  | cnf opening parsed closing =>
    cases second with
    | fof _ => simp [BodyKind] at kind
    | cnfFalse _ falsity _ =>
      have valid := cnfLiterals_head_valid parsed
      simp_all [HeadValid, atomic, Punct]
    | cnf _ other _ =>
      obtain ⟨rfl, rest⟩ := cnfLiterals_unique parsed other
      obtain ⟨rfl, rfl⟩ := List.cons.inj rest
      exact ⟨rfl, rfl⟩

theorem recordName_unique {token left right} (first : RecordName token left)
    (second : RecordName token right) : left = right := by
  obtain ⟨kind, firstKind, firstName⟩ := first
  obtain ⟨kind', secondKind, secondName⟩ := second
  have same := Kind.legacy.inj (firstKind.symm.trans secondKind)
  subst kind'
  exact Option.some.inj (firstName.symm.trans secondName)

/-- This theorem concerns source names, formula bodies and token consumption.
    Byte-span metadata remains bound by the actual decoder soundness theorem. -/
theorem declaration_content_unique {input left leftRest right rightRest}
    (first : DeclarationTokens input left leftRest) (second : DeclarationTokens input right rightRest) :
    left.name = right.name ∧ left.body = right.body ∧ leftRest = rightRest := by
  cases first with
  | declaration keyword opening name comma role roleComma parsed closing period =>
    cases second with
    | declaration keyword' opening' name' comma' role' roleComma' parsed' closing' period' =>
      obtain ⟨sameBody, sameRest⟩ := body_unique (by simpa using keyword.symm.trans keyword') parsed parsed'
      have rest := (List.cons.inj (List.cons.inj sameRest).2).2
      exact ⟨recordName_unique name name', sameBody, rest⟩

def contents (values : List Declaration) : List (Name × Body) :=
  values.map (fun declaration => (declaration.name, declaration.body))

theorem statements_content_unique {input left right}
    (first : StatementsTokens input left) (second : StatementsTokens input right) :
    contents left = contents right := by
  induction first generalizing right with
  | empty =>
    cases second with
    | empty => rfl
    | cons head _ => cases head
  | cons head tail ih =>
    cases second with
    | empty => cases head
    | cons other others =>
      obtain ⟨names, bodies, rfl⟩ := declaration_content_unique head other
      simp only [contents, List.map_cons]
      rw [names, bodies]
      exact congrArg (List.cons _) (ih others)

theorem statements_source_unique {input left right}
    (first : StatementsTokens input left) (second : StatementsTokens input right) : source left = source right := by
  have same := congrArg (List.map (fun value : Name × Body => value.2.formula))
    (statements_content_unique first second)
  simpa only [contents, source, List.map_map, Function.comp_def] using same

theorem byteParsed_source_unique {input maximum left right}
    (first : ByteParsed input maximum left) (second : ByteParsed input maximum right) : source left = source right := by
  obtain ⟨tokens, lexical, parsed, _⟩ := first
  obtain ⟨tokens', lexical', parsed', _⟩ := second
  have same := Except.ok.inj (lexical.symm.trans lexical')
  subst tokens'
  exact statements_source_unique parsed parsed'

end Fang.TptpCandidate.FullFof.Grammar
