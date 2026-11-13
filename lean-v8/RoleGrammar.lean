/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RoleInput

namespace Fang.TptpCandidate.Roles.Bytes
open FullFof

theorem roleOfName_sound {word role} (success : roleOfName word = some role) :
    word = roleName role := by
  unfold roleOfName at success
  split at success <;> first | (cases Option.some.inj success; rfl) | contradiction

def RoleToken (token : FullFof.Token) (role : Role) : Prop :=
  token.kind = .legacy (.lower (roleName role)) ∧ ∃ inputClass, classify role = .ok inputClass

theorem readRole_sound {endOffset token role} (success : readRole endOffset token = .ok role) :
    RoleToken token role := by
  unfold readRole at success
  split at success
  next word tokenKind =>
    cases parsedAt : roleOfName word with
    | none => simp [parsedAt, FullFof.failure] at success
    | some parsed =>
      cases inputAt : classify parsed with
      | error error => cases error <;> simp [parsedAt, inputAt, FullFof.failure] at success
      | ok inputClass =>
        have same : parsed = role := by simpa [parsedAt, inputAt, pure, Except.pure] using success
        subst role
        exact ⟨by simpa only [roleOfName_sound parsedAt] using tokenKind, ⟨inputClass, inputAt⟩⟩
  next _ => simp [FullFof.failure] at success

theorem header_exact {tokens header} (success : header? tokens = some header) : tokens = header.tokens := by
  unfold header? at success
  split at success
  · cases Option.some.inj success
    rfl
  · contradiction

/-- A consuming grammar reuses the independently proved body grammar after
    replacing exactly the header's role kind. RoleToken binds the original role.
    It makes no call to an executable declaration or formula decoder. -/
inductive DeclarationTokens : List FullFof.Token → Entry → List FullFof.Token → Prop where
  | declaration {header role original rest}
      (sourceRole : RoleToken header.role role)
      (goalKind : invalidGoal header role = false)
      (parsed : CnfBoolean.DeclarationTokens header.patched original rest) :
      DeclarationTokens header.tokens ⟨original, role, header.role.start, header.role.stop⟩ rest

theorem declaration_witness {seen endOffset tokens value final}
    (success : declaration seen endOffset tokens = .ok (value, final)) :
    ∃ header, tokens = header.tokens ∧
      readRole endOffset header.role = .ok value.role ∧ invalidGoal header value.role = false ∧
      CnfBoolean.declaration seen endOffset header.patched = .ok (value.original, final) ∧
      value.roleStart = header.role.start ∧ value.roleStop = header.role.stop := by
  unfold declaration at success
  cases headerAt : header? tokens with
  | none => simp [headerAt, FullFof.failure] at success
  | some header =>
    cases roleAt : readRole endOffset header.role with
    | error reason => simp [headerAt, roleAt, bind, Except.bind] at success
    | ok role =>
      cases valid : invalidGoal header role with
      | true => simp [headerAt, roleAt, valid, bind, Except.bind, FullFof.failure] at success
      | false =>
        cases resultAt : CnfBoolean.declaration seen endOffset header.patched with
        | error reason => simp [headerAt, roleAt, valid, resultAt, bind, Except.bind] at success
        | ok result =>
          rcases result with ⟨original, rest⟩
          have same : (⟨original, role, header.role.start, header.role.stop⟩, rest) = (value, final) := by
            simpa [headerAt, roleAt, valid, resultAt, bind, Except.bind, pure, Except.pure] using success
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
          exact ⟨header, header_exact headerAt, roleAt, valid, resultAt, rfl, rfl⟩

theorem declaration_sound {seen endOffset tokens value final}
    (success : declaration seen endOffset tokens = .ok (value, final)) :
    DeclarationTokens tokens value final ∧ value.original.name ∉ seen := by
  obtain ⟨header, shape, roleAt, valid, originalAt, start, stop⟩ := declaration_witness success
  have original := CnfBoolean.declaration_sound originalAt
  constructor
  · have same : value = ⟨value.original, value.role, header.role.start, header.role.stop⟩ := by
      cases value
      simp_all
    rw [shape, same]
    exact .declaration (readRole_sound roleAt) valid original.1
  · exact original.2

inductive StatementsTokens : List FullFof.Token → List Entry → Prop where
  | empty : StatementsTokens [] []
  | cons {tokens first rest values} (head : DeclarationTokens tokens first rest)
      (tail : StatementsTokens rest values) : StatementsTokens tokens (first :: values)

def ByteParsed (input : List UInt8) (maximum : Nat) (values : List Entry) : Prop :=
  ∃ tokens, FullFof.tokenizeBytes input maximum = .ok tokens ∧ StatementsTokens tokens values ∧
    (values.map (fun value => value.original.name)).Nodup ∧ modesValid values = true

end Fang.TptpCandidate.Roles.Bytes
