/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import CnfBooleanProblemSound

namespace Fang.TptpCandidate.FullFof.CnfBoolean

theorem declaration_closed {seen endOffset input value final}
    (success : declaration seen endOffset input = .ok (value, final)) :
    match value.body with | .cnf _ => True | .fof body => body.Within [] := by
  cases input with
  | nil => simp [declaration, failure] at success
  | cons keyword rest =>
    simp only [declaration, failure, bind, Except.bind, pure, Except.pure] at success
    repeat' first | contradiction | split at success
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success); trivial
    · rename_i _ keywordAt _ opened openAt _ nameToken afterName nameInput
        _ nameKind nameKindAt _ name nameAt fresh _ roleComma roleCommaAt
        _ role afterRole roleInput _ roleAt _ bodyComma bodyCommaAt _
        _ body bodyAt noAnnotation _ closing closingAt _ dot dotAt
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      exact formula_within bodyAt

theorem declarations_closed {fuel seen endOffset input values}
    (success : declarations fuel seen endOffset input = .ok values) : Grammar.Closed values := by
  induction fuel generalizing seen input values with
  | zero => simp [declarations, failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarations] at success
      subst values
      simp [Grammar.Closed]
    | cons token rest =>
      unfold declarations at success
      simp only [failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact declaration_closed firstAt
      · exact ih tailAt value member

theorem decode_closed {input maximum values}
    (success : decodeBytes input maximum = .ok values) : Grammar.Closed values := by
  obtain ⟨tokens, _, parsed⟩ := decode_has_tokens success
  exact declarations_closed parsed


end Fang.TptpCandidate.FullFof.CnfBoolean
