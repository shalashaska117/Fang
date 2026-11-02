/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import CnfBooleanProblemInput

namespace Fang.TptpCandidate.FullFof.CnfBoolean
open Grammar

inductive StatementsTokens : List Token → List Declaration → Prop where
  | empty : StatementsTokens [] []
  | cons {input first middle rest} (head : DeclarationTokens input first middle)
      (tail : StatementsTokens middle rest) : StatementsTokens input (first :: rest)


theorem declarations_sound {fuel seen endOffset input values}
    (success : declarations fuel seen endOffset input = .ok values) :
    StatementsTokens input values ∧ WellNamed values ∧
      ∀ name ∈ values.map Declaration.name, name ∉ seen := by
  induction fuel generalizing seen input values with
  | zero => simp [declarations, failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarations] at success
      subst values
      exact ⟨.empty, by simp [WellNamed], by simp⟩
    | cons token rest =>
      by_cases large : seen.length ≥ 1000
      · simp [declarations, large, failure, bind, Except.bind] at success
      · cases firstAt : declaration seen endOffset (token :: rest) with
        | error error => simp [declarations, large, firstAt, bind, Except.bind] at success
        | ok result =>
          rcases result with ⟨first, afterFirst⟩
          cases tailAt : declarations fuel (first.name :: seen) endOffset afterFirst with
          | error error => simp [declarations, large, firstAt, tailAt, bind, Except.bind] at success
          | ok more =>
            simp [declarations, large, firstAt, tailAt, bind, Except.bind, pure, Except.pure] at success
            subst values
            obtain ⟨firstParsed, firstFresh⟩ := declaration_sound firstAt
            obtain ⟨moreParsed, moreUnique, moreFresh⟩ := ih tailAt
            refine ⟨.cons firstParsed moreParsed, ?_, ?_⟩
            · simp only [WellNamed, List.map_cons, List.nodup_cons] at *
              exact ⟨fun member => moreFresh first.name member (by simp), moreUnique⟩
            · intro name member
              simp only [List.map_cons, List.mem_cons] at member
              rcases member with rfl | member
              · exact firstFresh
              · exact fun old => moreFresh name member (by simp [old])


/-- Token grammar and unique source labels are independent of the parser.
    The lexical boundary uses the frozen eight-connective byte lexer. -/
def ByteParsed (input : List UInt8) (maximum : Nat) (values : List Declaration) : Prop :=
  ∃ tokens, tokenizeBytes input maximum = .ok tokens ∧
    StatementsTokens tokens values ∧ WellNamed values


theorem decode_has_tokens {input maximum values}
    (success : decodeBytes input maximum = .ok values) :
    ∃ tokens, tokenizeBytes input maximum = .ok tokens ∧
      declarations (tokens.length + 1) [] input.length tokens = .ok values := by
  unfold decodeBytes at success
  cases lexical : tokenizeBytes input maximum with
  | error reason => simp [lexical, bind, Except.bind] at success
  | ok tokens => exact ⟨tokens, rfl, by simpa [lexical, bind, Except.bind] using success⟩

theorem decode_grammar {input maximum values}
    (success : decodeBytes input maximum = .ok values) : ByteParsed input maximum values := by
  obtain ⟨tokens, lexical, parsed⟩ := decode_has_tokens success
  obtain ⟨grammar, unique, _⟩ := declarations_sound parsed
  exact ⟨tokens, lexical, grammar, unique⟩

theorem decode_names_nodup {input maximum values}
    (success : decodeBytes input maximum = .ok values) : (values.map Declaration.name).Nodup := by
  obtain ⟨_, _, _, unique⟩ := decode_grammar success
  exact unique

theorem source_declaration_order (values : List Declaration) :
    source values = values.map (fun declaration => declaration.body.formula) := rfl

theorem decode_retained_names {input maximum values}
    (success : decodeBytes input maximum = .ok values) :
    ∃ tokens, tokenizeBytes input maximum = .ok tokens ∧ StatementsTokens tokens values ∧
      (values.map Declaration.name).Nodup ∧
      source values = values.map (fun declaration => declaration.body.formula) := by
  obtain ⟨tokens, lexical, grammar, unique⟩ := decode_grammar success
  exact ⟨tokens, lexical, grammar, unique, source_declaration_order values⟩


end Fang.TptpCandidate.FullFof.CnfBoolean
