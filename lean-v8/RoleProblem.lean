/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RoleGrammar

namespace Fang.TptpCandidate.Roles.Bytes
open FullFof

def WellNamed (values : List Entry) : Prop :=
  (values.map (fun value => value.original.name)).Nodup

theorem declarations_sound {fuel seen endOffset input values}
    (success : declarations fuel seen endOffset input = .ok values) :
    StatementsTokens input values ∧ WellNamed values ∧
      ∀ name ∈ values.map (fun value => value.original.name), name ∉ seen := by
  induction fuel generalizing seen input values with
  | zero => simp [declarations, FullFof.failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarations] at success
      subst values
      exact ⟨.empty, by simp [WellNamed], by simp⟩
    | cons token rest =>
      by_cases large : seen.length ≥ 1000
      · simp [declarations, large, FullFof.failure, bind, Except.bind] at success
      · cases firstAt : declaration seen endOffset (token :: rest) with
        | error error => simp [declarations, large, firstAt, bind, Except.bind] at success
        | ok result =>
          rcases result with ⟨first, afterFirst⟩
          cases tailAt : declarations fuel (first.original.name :: seen) endOffset afterFirst with
          | error error => simp [declarations, large, firstAt, tailAt, bind, Except.bind] at success
          | ok more =>
            simp [declarations, large, firstAt, tailAt, bind, Except.bind, pure, Except.pure] at success
            subst values
            obtain ⟨firstParsed, firstFresh⟩ := declaration_sound firstAt
            obtain ⟨moreParsed, moreUnique, moreFresh⟩ := ih tailAt
            refine ⟨.cons firstParsed moreParsed, ?_, ?_⟩
            · simp only [WellNamed, List.map_cons, List.nodup_cons] at *
              exact ⟨fun member => moreFresh first.original.name member (by simp), moreUnique⟩
            · intro name member
              simp only [List.map_cons, List.mem_cons] at member
              rcases member with rfl | member
              · exact firstFresh
              · exact fun old => moreFresh name member (by simp [old])

theorem decode_has_tokens {input maximum values}
    (success : decodeBytes input maximum = .ok values) :
    ∃ tokens, FullFof.tokenizeBytes input maximum = .ok tokens ∧
      declarations (tokens.length + 1) [] input.length tokens = .ok values ∧
      modesValid values = true := by
  unfold decodeBytes at success
  cases lexical : FullFof.tokenizeBytes input maximum with
  | error reason => simp [lexical, bind, Except.bind] at success
  | ok tokens =>
    cases parsed : declarations (tokens.length + 1) [] input.length tokens with
    | error reason => simp [lexical, parsed, bind, Except.bind] at success
    | ok result =>
      by_cases valid : modesValid result = true
      · simp [lexical, parsed, valid, bind, Except.bind, pure, Except.pure] at success
        subst values
        exact ⟨tokens, rfl, parsed, valid⟩
      · simp [lexical, parsed, valid, bind, Except.bind, FullFof.failure] at success

theorem decode_grammar {input maximum values}
    (success : decodeBytes input maximum = .ok values) : ByteParsed input maximum values := by
  obtain ⟨tokens, lexical, parsed, valid⟩ := decode_has_tokens success
  obtain ⟨grammar, unique, _⟩ := declarations_sound parsed
  exact ⟨tokens, lexical, grammar, unique, valid⟩

theorem decode_names_nodup {input maximum values}
    (success : decodeBytes input maximum = .ok values) : WellNamed values := by
  obtain ⟨_, _, _, unique, _⟩ := decode_grammar success
  exact unique

def Closed (values : List Entry) : Prop :=
  ∀ value ∈ values, match value.original.body with | .cnf _ => True | .fof body => body.Within []

theorem declaration_closed {seen endOffset tokens value final}
    (success : declaration seen endOffset tokens = .ok (value, final)) :
    match value.original.body with | .cnf _ => True | .fof body => body.Within [] := by
  obtain ⟨_, _, _, _, original, _, _⟩ := declaration_witness success
  exact CnfBoolean.declaration_closed original

theorem declarations_closed {fuel seen endOffset input values}
    (success : declarations fuel seen endOffset input = .ok values) : Closed values := by
  induction fuel generalizing seen input values with
  | zero => simp [declarations, FullFof.failure] at success
  | succ fuel ih =>
    cases input with
    | nil =>
      simp [declarations] at success
      subst values
      simp [Closed]
    | cons token rest =>
      unfold declarations at success
      simp only [FullFof.failure, bind, Except.bind, pure, Except.pure] at success
      repeat' first | contradiction | split at success
      rename_i notLarge _ first firstAt _ tail tailAt
      obtain rfl := Except.ok.inj success
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact declaration_closed firstAt
      · exact ih tailAt value member

theorem decode_closed {input maximum values}
    (success : decodeBytes input maximum = .ok values) : Closed values := by
  obtain ⟨_, _, parsed, _⟩ := decode_has_tokens success
  exact declarations_closed parsed

end Fang.TptpCandidate.Roles.Bytes
