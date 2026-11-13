/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RoleProblem

namespace Fang.TptpCandidate.Roles.Bytes
open FullFof

theorem roleName_roundtrip (role : Role) : roleOfName (roleName role) = some role := by
  cases role <;> rfl

theorem roleName_injective : Function.Injective roleName := by
  intro left right same
  have names := congrArg roleOfName same
  simpa only [roleName_roundtrip, Option.some.injEq] using names

theorem roleToken_unique {token left right}
    (first : RoleToken token left) (second : RoleToken token right) : left = right := by
  apply roleName_injective
  simpa using first.1.symm.trans second.1

theorem header_tokens_injective : Function.Injective Header.tokens := by
  intro left right same
  have headers := congrArg header? same
  simpa only [Header.tokens, header?, Option.some.injEq] using headers

theorem declaration_view {input value rest} (parsed : DeclarationTokens input value rest) :
    ∃ header : Header, input = header.tokens ∧ RoleToken header.role value.role ∧
      CnfBoolean.DeclarationTokens header.patched value.original rest := by
  cases parsed with
  | declaration sourceRole _ body => exact ⟨_, rfl, sourceRole, body⟩

/-- Names, roles, original bodies and token remainders are unique. Arbitrary
    source metadata offset uniqueness is not claimed. -/
theorem declaration_content_unique {input left leftRest right rightRest}
    (first : DeclarationTokens input left leftRest) (second : DeclarationTokens input right rightRest) :
    left.original.name = right.original.name ∧ left.role = right.role ∧
      left.original.body = right.original.body ∧ leftRest = rightRest := by
  obtain ⟨leftHeader, leftShape, leftRole, leftBody⟩ := declaration_view first
  obtain ⟨rightHeader, rightShape, rightRole, rightBody⟩ := declaration_view second
  have headers := header_tokens_injective (leftShape.symm.trans rightShape)
  subst rightHeader
  obtain ⟨names, bodies, rest⟩ := CnfBoolean.declaration_content_unique leftBody rightBody
  exact ⟨names, roleToken_unique leftRole rightRole, bodies, rest⟩

def contents (values : List Entry) : List (Name × Role × FullFof.Body) :=
  values.map (fun value => (value.original.name, value.role, value.original.body))

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
      obtain ⟨names, roles, bodies, rfl⟩ := declaration_content_unique head other
      simp only [contents, List.map_cons]
      rw [names, roles, bodies]
      exact congrArg (List.cons _) (ih others)

theorem byteParsed_content_unique {input maximum left right}
    (first : ByteParsed input maximum left) (second : ByteParsed input maximum right) :
    contents left = contents right := by
  obtain ⟨tokens, lexical, parsed, _, _⟩ := first
  obtain ⟨otherTokens, otherLexical, otherParsed, _, _⟩ := second
  have same := Except.ok.inj (lexical.symm.trans otherLexical)
  subst otherTokens
  exact statements_content_unique parsed otherParsed

end Fang.TptpCandidate.Roles.Bytes
