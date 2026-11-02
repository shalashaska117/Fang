/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import CnfBooleanUnique

namespace Fang.TptpCandidate.FullFof.CnfBoolean
open Grammar

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

end Fang.TptpCandidate.FullFof.CnfBoolean
