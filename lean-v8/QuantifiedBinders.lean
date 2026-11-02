/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Decoder construction proof draft. It is not part of an accepted gate yet. -/
import QuantifiedInput
import QuantifiedGrammar
import FOFTermGrammar
import Fang.FrontendClauseState
import Fang.FrontendLiteralRun

namespace Fang.QuantifiedFrontend
open Frontend FOFFrontend

abbrev BinderNames (state : State) :=
  Source.RelatedLists (fun name id => namedIndex name state.variables 0 = some id)

theorem BinderNames.extend {before after names ids} (encoded : BinderNames before names ids)
    (extension : TableExtension before after) : BinderNames after names ids := by
  induction encoded with
  | nil => exact .nil
  | cons head tail ih => exact .cons (extension.variables _ _ head) ih

def BindersResult (before : State) (ids : List Nat) (after : State) : Prop :=
  ∃ names, BinderNames after names ids ∧ TableExtension before after ∧
    NamedQuantified.Grammar.BindersTokens (spellings before) names (spellings after)

theorem binders_result (fuel : Nat) :
    ∀ {state ids updated}, binders fuel state = .ok (ids, updated) →
      BindersResult state ids updated := by
  induction fuel with
  | zero => intro state ids updated success; simp [binders, fail_run] at success
  | succ fuel ih =>
    intro state ids updated success
    simp only [binders] at success
    obtain ⟨offset, before, positioned, success⟩ := parser_bind_success success
    rw [position_run] at positioned
    cases positioned
    obtain ⟨name, consumed, consumedRun, success⟩ := parser_bind_success success
    cases valid : variableName name with
    | false => simp [valid, bind, StateT.bind, failAt_run, Except.bind] at success
    | true =>
      simp only [valid, Bool.not_true, Bool.false_eq_true, ite_false] at success
      obtain ⟨id, allocated, allocatedRun, success⟩ := parser_bind_success success
      obtain ⟨actualId, actualState, actualRun, allocation, tokenFrame, _⟩ := variableId_spec name consumed
      rw [allocatedRun] at actualRun
      cases actualRun
      have found : namedIndex name allocated.variables 0 = some id :=
        (namedIndex_first_iff _ _ _).mpr allocation.1
      have initialExtension := (consume_tableExtension consumedRun).trans
        (variableId_tableExtension name consumed allocated id allocatedRun)
      have sourceName : Source.Grammar.VariableName name :=
        (variableName_iff name (variableName_ascii valid)).mp valid
      obtain ⟨delimiter, beforeDelimiter, peeked, success⟩ := parser_bind_success success
      rw [peek_run] at peeked
      cases peeked
      split at success
      · obtain ⟨ignored, final, closed, success⟩ := parser_bind_success success
        cases ignored
        cases Except.ok.inj success
        have closeExtension := expect_tableExtension closed
        refine ⟨[name], .cons (closeExtension.variables _ _ found) .nil,
          initialExtension.trans closeExtension, ?_⟩
        have shape : spellings state = name :: "]" :: spellings updated := by
          rw [consume_spellings consumedRun]
          have same : spellings consumed = spellings allocated := by simp [spellings, tokenFrame]
          rw [same, expect_spellings closed]
        rw [shape]
        exact .last sourceName
      · split at success
        · obtain ⟨ignored, afterComma, comma, success⟩ := parser_bind_success success
          cases ignored
          obtain ⟨tail, final, child, success⟩ := parser_bind_success success
          cases Except.ok.inj success
          obtain ⟨names, encoding, extension, grammar⟩ := ih child
          have commaExtension := expect_tableExtension comma
          refine ⟨name :: names,
            .cons (extension.variables _ _ (commaExtension.variables _ _ found)) encoding,
            initialExtension.trans (commaExtension.trans extension), ?_⟩
          have shape : spellings state = name :: "," :: spellings afterComma := by
            rw [consume_spellings consumedRun]
            have same : spellings consumed = spellings allocated := by simp [spellings, tokenFrame]
            rw [same, expect_spellings comma]
          rw [shape]
          exact .more sourceName grammar
        · split at success <;> simp [fail_run] at success

end Fang.QuantifiedFrontend
