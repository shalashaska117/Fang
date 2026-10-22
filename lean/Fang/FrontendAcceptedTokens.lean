/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Successful parsing classifies the consumed raw tokens. The proof works
backwards from a classified remainder, without assuming a valid whole input.
-/
import Fang.FrontendTokenView
import Fang.FrontendClauseState
import Fang.FrontendTokenPreservation

namespace Fang.Frontend

open Source.Grammar

def TokensClassifiable (tokens : List Token) : Prop :=
  ∀ raw ∈ tokens, ∃ token, RawTokenSpelling raw token

def TextClassifiable (text : String) : Prop :=
  ∀ raw : Token, raw.text = text → ∃ token, RawTokenSpelling raw token

theorem textClassifiable_lower (name : String) (valid : lowerName name = true) :
    TextClassifiable name := by
  intro raw same
  have validRaw : lowerName raw.text = true := by simpa only [same] using valid
  exact ⟨_, rawTokenSpelling_lower raw (lowerName_ascii validRaw) validRaw⟩

theorem textClassifiable_variable (name : String) (valid : variableName name = true) :
    TextClassifiable name := by
  intro raw same
  have validRaw : variableName raw.text = true := by simpa only [same] using valid
  exact ⟨_, rawTokenSpelling_variable raw (variableName_ascii validRaw) validRaw⟩

theorem textClassifiable_punctuation (character : Char) (valid : RawPunctuation character)
    (token : Source.Grammar.Token) (spelled : Source.Grammar.Punctuation (asciiByte character) token) :
    TextClassifiable (String.singleton character) := by
  intro raw same
  exact ⟨token, rawTokenSpelling_punctuation raw character valid same token spelled⟩

theorem textClassifiable_expected (wanted : String)
    (known : wanted ∈ ["cnf", "(", ")", ",", ".", "axiom", "|", "~", "$false"]) :
    TextClassifiable wanted := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact textClassifiable_lower "cnf" (by decide)
  · exact textClassifiable_punctuation '(' (by simp [RawPunctuation]) .lparen .lparen
  · exact textClassifiable_punctuation ')' (by simp [RawPunctuation]) .rparen .rparen
  · exact textClassifiable_punctuation ',' (by simp [RawPunctuation]) .comma .comma
  · exact textClassifiable_punctuation '.' (by simp [RawPunctuation]) .period .period
  · exact textClassifiable_lower "axiom" (by decide)
  · exact textClassifiable_punctuation '|' (by simp [RawPunctuation]) .disjoin .disjoin
  · exact textClassifiable_punctuation '~' (by simp [RawPunctuation]) .negate .negate
  · intro raw same
    exact ⟨.falseLiteral, rawTokenSpelling_false raw same⟩

theorem TokensClassifiable.to_classified {raw : List Token} (valid : TokensClassifiable raw) :
    ∃ tokens, ClassifiedTokens raw tokens := by
  induction raw with
  | nil => exact ⟨[], .nil⟩
  | cons head tail induction =>
      obtain ⟨token, spelled⟩ := valid head (by simp)
      obtain ⟨tokens, classified⟩ := induction (fun item member => valid item (by simp [member]))
      exact ⟨token :: tokens, .cons spelled classified⟩

def RestoresClassification {α : Type} (parser : Parser α) : Prop :=
  ∀ (state : State) (value : α) (final : State),
    parser state = .ok (value, final) → TokensClassifiable final.tokens → TokensClassifiable state.tokens

theorem restores_bind {α β : Type} {head : Parser α} {tail : α → Parser β}
    (first : RestoresClassification head) (rest : ∀ value, RestoresClassification (tail value)) :
    RestoresClassification (head >>= tail) := by
  intro state value final success valid
  obtain ⟨intermediate, updated, headRun, tailRun⟩ := parser_bind_success success
  exact first state intermediate updated headRun (rest intermediate updated value final tailRun valid)

theorem restores_frame {α : Type} {parser : Parser α}
    (frame : ∀ state value final, parser state = .ok (value, final) → final.tokens = state.tokens) :
    RestoresClassification parser := by
  intro state value final success valid
  simpa only [frame state value final success] using valid

theorem restores_pure {α : Type} (value : α) : RestoresClassification (pure value) := by
  apply restores_frame
  intro state result final success
  have same : (value, state) = (result, final) := Except.ok.inj success
  cases same
  rfl

theorem restores_peek : RestoresClassification peek := by
  apply restores_frame
  intro state value final success
  have same := congrArg Prod.snd (Except.ok.inj success)
  cases same
  rfl

theorem restores_position : RestoresClassification position := by
  apply restores_frame
  intro state value final success
  have same := congrArg Prod.snd (Except.ok.inj success)
  cases same
  rfl

theorem restores_expect (wanted : String)
    (known : wanted ∈ ["cnf", "(", ")", ",", ".", "axiom", "|", "~", "$false"]) :
    RestoresClassification (expect wanted) := by
  intro state value final success valid
  cases value
  obtain ⟨raw, rest, shape, text, rfl⟩ := expect_success success
  intro token member
  rw [shape] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact textClassifiable_expected wanted known token text
  · exact valid token member

theorem restores_fail {α : Type} (reason : String) : RestoresClassification (fail (α := α) reason) := by
  intro state value final success valid
  simp [fail_run] at success

theorem restores_failAt {α : Type} (offset : Nat) (reason : String) :
    RestoresClassification (failAt (α := α) offset reason) := by
  intro state value final success valid
  simp [failAt_run] at success

theorem restores_fail_bind {α β : Type} (reason : String) (tail : α → Parser β) :
    RestoresClassification (fail reason >>= tail) := by
  intro state value final success valid
  simp [bind, StateT.bind, fail_run, Except.bind] at success

theorem restores_failAt_bind {α β : Type} (offset : Nat) (reason : String) (tail : α → Parser β) :
    RestoresClassification (failAt offset reason >>= tail) := by
  intro state value final success valid
  simp [bind, StateT.bind, failAt_run, Except.bind] at success

theorem restores_variableId (name : String) : RestoresClassification (variableId name) :=
  restores_frame (fun state value final success => variableId_preserves_tokens name state final value success)

theorem restores_reserveSymbol (predicate : Bool) (name : String) :
    RestoresClassification (reserveSymbol predicate name) :=
  restores_frame (fun state value final success => reserveSymbol_preserves_tokens predicate name state final value success)

theorem restores_checkArity (predicate : Bool) (id arity offset : Nat) :
    RestoresClassification (checkArity predicate id arity offset) := by
  apply restores_frame
  intro state value final success
  cases value
  exact checkArity_preserves_tokens predicate id arity offset state final success

theorem restores_consume_valid {α : Type} {tail : String → Parser α}
    (checked : ∀ name state value final, tail name state = .ok (value, final) → TextClassifiable name)
    (restored : ∀ name, RestoresClassification (tail name)) :
    RestoresClassification (consume >>= tail) := by
  intro state value final success valid
  obtain ⟨name, updated, headRun, tailRun⟩ := parser_bind_success success
  obtain ⟨raw, rest, shape, text, rfl⟩ := consume_success headRun
  have remaining := restored name _ value final tailRun valid
  intro token member
  rw [shape] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact checked name _ value final tailRun token text
  · exact remaining token member

theorem restores_term_of_terms {fuel : Nat} (arguments : RestoresClassification (terms fuel)) :
    RestoresClassification (term (fuel + 1)) := by
  simp only [term]
  apply restores_bind restores_position
  intro offset
  apply restores_consume_valid
  · intro name state value final success
    split at success
    · exact textClassifiable_variable name ‹variableName name = true›
    · split at success
      · exact textClassifiable_lower name ‹lowerName name = true›
      · simp [failAt_run] at success
  · intro name
    split
    · exact restores_bind (restores_variableId name) (fun _ => restores_pure _)
    · split
      · apply restores_bind (restores_reserveSymbol false name)
        intro id
        apply restores_bind restores_peek
        intro next
        split
        · apply restores_bind (restores_expect "(" (by decide))
          intro ignored
          apply restores_bind arguments
          intro args
          apply restores_bind (restores_expect ")" (by decide))
          intro ignored
          apply restores_bind (restores_pure args)
          intro returnedArgs
          exact restores_bind (restores_checkArity false id returnedArgs.length offset)
            (fun _ => restores_pure _)
        · apply restores_bind (restores_pure [])
          intro args
          exact restores_bind (restores_checkArity false id args.length offset) (fun _ => restores_pure _)
      · exact restores_failAt _ _

theorem restores_terms_of_terms {fuel : Nat}
    (one : RestoresClassification (term fuel)) (rest : RestoresClassification (terms fuel)) :
    RestoresClassification (terms (fuel + 1)) := by
  simp only [terms]
  apply restores_bind one
  intro first
  apply restores_bind restores_peek
  intro next
  split
  · apply restores_bind (restores_expect "," (by decide))
    intro ignored
    exact restores_bind rest (fun _ => restores_pure _)
  · exact restores_pure _

theorem restores_term_terms (fuel : Nat) :
    RestoresClassification (term fuel) ∧ RestoresClassification (terms fuel) := by
  induction fuel with
  | zero => exact ⟨restores_fail _, restores_fail _⟩
  | succ fuel induction => exact ⟨restores_term_of_terms induction.2,
      restores_terms_of_terms induction.1 induction.2⟩

theorem restores_literal (fuel : Nat) : RestoresClassification (literal fuel) := by
  simp only [literal]
  apply restores_bind restores_peek
  intro next
  split
  · apply restores_bind (restores_expect "~" (by decide))
    intro ignored
    apply restores_bind (restores_pure false)
    intro positive
    apply restores_bind restores_position
    intro offset
    apply restores_consume_valid
    · intro name state value final success
      split at success
      · simp [bind, StateT.bind, failAt_run, Except.bind] at success
      · exact textClassifiable_lower name (by simpa using ‹¬(!lowerName name) = true›)
    · intro name
      split
      · exact restores_failAt_bind _ _ _
      · apply restores_bind (restores_reserveSymbol true name)
        intro pred
        apply restores_bind restores_peek
        intro next
        split
        · apply restores_bind (restores_expect "(" (by decide))
          intro ignored
          apply restores_bind (restores_term_terms fuel).2
          intro args
          apply restores_bind (restores_expect ")" (by decide))
          intro ignored
          apply restores_bind (restores_pure args)
          intro returnedArgs
          exact restores_bind (restores_checkArity true pred returnedArgs.length offset)
            (fun _ => restores_pure _)
        · apply restores_bind (restores_pure [])
          intro args
          exact restores_bind (restores_checkArity true pred args.length offset) (fun _ => restores_pure _)
  · apply restores_bind (restores_pure true)
    intro positive
    apply restores_bind restores_position
    intro offset
    apply restores_consume_valid
    · intro name state value final success
      split at success
      · simp [bind, StateT.bind, failAt_run, Except.bind] at success
      · exact textClassifiable_lower name (by simpa using ‹¬(!lowerName name) = true›)
    · intro name
      split
      · exact restores_failAt_bind _ _ _
      · apply restores_bind (restores_reserveSymbol true name)
        intro pred
        apply restores_bind restores_peek
        intro next
        split
        · apply restores_bind (restores_expect "(" (by decide))
          intro ignored
          apply restores_bind (restores_term_terms fuel).2
          intro args
          apply restores_bind (restores_expect ")" (by decide))
          intro ignored
          apply restores_bind (restores_pure args)
          intro returnedArgs
          exact restores_bind (restores_checkArity true pred returnedArgs.length offset)
            (fun _ => restores_pure _)
        · apply restores_bind (restores_pure [])
          intro args
          exact restores_bind (restores_checkArity true pred args.length offset) (fun _ => restores_pure _)

theorem restores_literals (fuel : Nat) : RestoresClassification (literals fuel) := by
  induction fuel with
  | zero => exact restores_fail _
  | succ fuel induction =>
      simp only [literals]
      apply restores_bind (restores_literal fuel)
      intro first
      apply restores_bind restores_peek
      intro next
      split
      · apply restores_bind (restores_expect "|" (by decide))
        intro ignored
        exact restores_bind induction (fun _ => restores_pure _)
      · exact restores_pure _

theorem restores_clause_update {α : Type} (name : String) (offset : Nat)
    (rest : Parser α) (restored : RestoresClassification rest) :
    RestoresClassification (do
      let state ← get
      if state.clauseNames.contains name then
        failAt offset s!"invalid-syntax: duplicate clause name '{name}'"
      set { state with clauseNames := state.clauseNames ++ [name], variables := [] }
      rest) := by
  intro state value final success valid
  obtain ⟨_, tail⟩ := (clause_update_success_iff name offset rest state final value).mp success
  exact restored { state with clauseNames := state.clauseNames ++ [name], variables := [] }
    value final tail valid

theorem restores_statement (fuel : Nat) : RestoresClassification (statement fuel) := by
  simp only [statement]
  apply restores_bind restores_peek
  intro next
  split
  · exact restores_fail_bind _ _
  · apply restores_bind (restores_expect "cnf" (by decide))
    intro ignored
    apply restores_bind (restores_expect "(" (by decide))
    intro ignored
    apply restores_bind restores_position
    intro offset
    apply restores_consume_valid
    · intro name state value final success
      split at success
      · simp [bind, StateT.bind, failAt_run, Except.bind] at success
      · exact textClassifiable_lower name (by simpa using ‹¬(!lowerName name) = true›)
    · intro name
      split
      · exact restores_failAt_bind _ _ _
      · apply restores_clause_update name offset
        apply restores_bind (restores_expect "," (by decide))
        intro ignored
        apply restores_bind restores_peek
        intro next
        split
        · exact restores_fail_bind _ _
        · apply restores_bind (restores_expect "axiom" (by decide))
          intro ignored
          apply restores_bind (restores_expect "," (by decide))
          intro ignored
          apply restores_bind (restores_expect "(" (by decide))
          intro ignored
          apply restores_bind restores_peek
          intro next
          split
          · apply restores_bind (restores_expect "$false" (by decide))
            intro ignored
            apply restores_bind (restores_pure [])
            intro body
            apply restores_bind (restores_expect ")" (by decide))
            intro ignored
            apply restores_bind (restores_expect ")" (by decide))
            intro ignored
            exact restores_bind (restores_expect "." (by decide)) (fun _ => restores_pure _)
          · apply restores_bind (restores_literals fuel)
            intro body
            apply restores_bind (restores_expect ")" (by decide))
            intro ignored
            apply restores_bind (restores_expect ")" (by decide))
            intro ignored
            exact restores_bind (restores_expect "." (by decide)) (fun _ => restores_pure _)

theorem restores_statements (fuel : Nat) : RestoresClassification (statements fuel) := by
  induction fuel with
  | zero => exact restores_fail _
  | succ fuel induction =>
      simp only [statements]
      apply restores_bind restores_peek
      intro next
      split
      · exact restores_pure _
      · apply restores_bind (restores_statement fuel)
        intro first
        exact restores_bind induction (fun _ => restores_pure _)

theorem statements_classifies_input {fuel : Nat} {state final : State} {problem : Problem}
    (success : statements fuel state = .ok (problem, final)) :
    ∃ tokens, ClassifiedTokens state.tokens tokens := by
  have empty := (statements_success_consumes_all success).1
  have validFinal : TokensClassifiable final.tokens := by
    simp [TokensClassifiable, empty]
  exact (restores_statements fuel state problem final success validFinal).to_classified

#print axioms restores_term_terms
#print axioms restores_literal
#print axioms restores_statement
#print axioms statements_classifies_input

end Fang.Frontend
