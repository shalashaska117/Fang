/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Grammar and semantic encoding of successful disjunction parsing.
-/
import Fang.FrontendLiteralGrammar

namespace Fang.Source.Grammar

inductive DisjunctionPrefix : List Token → List Literal → List Token → Prop where
  | last {input rest literal} (head : LiteralTokens input literal rest)
      (noDisjoin : rest.head? ≠ some .disjoin) : DisjunctionPrefix input [literal] rest
  | more {input middle rest literal literals}
      (head : LiteralTokens input literal (.disjoin :: middle))
      (tail : DisjunctionPrefix middle literals rest) : DisjunctionPrefix input (literal :: literals) rest

theorem DisjunctionPrefix.body {input literals rest}
    (parsed : DisjunctionPrefix input literals (.rparen :: rest)) : DisjunctionTokens input literals rest := by
  generalize ending : Source.Grammar.Token.rparen :: rest = output at parsed
  induction parsed with
  | last head noDisjoin => exact .last (ending ▸ head)
  | more head tail induction => exact .more head (induction ending)

end Fang.Source.Grammar

namespace Fang.Frontend

open Source.Grammar

abbrev TableClauseEncoding (state : State) (named : List Source.Literal) (encoded : Clause) : Prop :=
  Source.RelatedLists (TableLiteralEncoding state) named encoded

theorem TableClauseEncoding.extend {before after named encoded}
    (encoding : TableClauseEncoding before named encoded) (extension : TableExtension before after) :
    TableClauseEncoding after named encoded := by
  induction encoding with
  | nil => exact .nil
  | cons head tail induction => exact .cons (head.extend extension) induction

theorem TableClauseEncoding.toSource {state named encoded} (name : String)
    (encoding : TableClauseEncoding state named encoded) :
    Source.ClauseEncoding (signatureFrom state) (symbolsFrom state)
      (variablesFrom state.variables) ⟨name, named⟩ encoded := by
  induction encoding with
  | nil => exact .nil
  | cons head tail induction => exact .cons head.toSource induction

theorem RawTokenSpelling.is_disjoin {raw : Token} {token : Source.Grammar.Token}
    (classified : RawTokenSpelling raw token) : raw.text = "|" ↔ token = .disjoin := by
  constructor
  · intro text
    exact classified.unique (rawTokenSpelling_punctuation raw '|' (by simp [RawPunctuation]) text .disjoin .disjoin)
  · intro same
    simpa [same, Source.Grammar.Token.text] using classified.text

theorem ClassifiedTokens.head_disjoin {raw : List Token} {tokens : List Source.Grammar.Token}
    (classified : ClassifiedTokens raw tokens) :
    raw.head?.map Token.text = some "|" ↔ tokens.head? = some .disjoin := by
  cases classified with
  | nil => simp
  | cons head tail => simpa using head.is_disjoin

theorem literals_run (fuel : Nat) (state : State) :
    literals (fuel + 1) state = (do
      let (first, afterFirst) ← literal fuel state
      if afterFirst.tokens.head?.map Token.text == some "|" then do
        let (_, consumed) ← expect "|" afterFirst
        let (rest, updated) ← literals fuel consumed
        pure (first :: rest, updated)
      else .ok ([first], afterFirst)) := by
  simp only [literals, peek, bind, pure, get, getThe, MonadStateOf.get,
    StateT.bind, StateT.get, StateT.pure, Except.pure, Except.bind]
  cases result : literal fuel state with
  | error error => rfl
  | ok pair =>
      dsimp only
      split <;> rfl

def LiteralsGrammarResult (before : State) (tokens : List Source.Grammar.Token)
    (encoded : Clause) (after : State) : Prop :=
  ∃ named rest, TableClauseEncoding after named encoded ∧ TableExtension before after ∧
    DisjunctionPrefix tokens named rest ∧ ClassifiedTokens after.tokens rest

theorem literals_grammar {fuel state input encoded updated}
    (classified : ClassifiedTokens state.tokens input)
    (success : literals fuel state = .ok (encoded, updated)) :
    LiteralsGrammarResult state input encoded updated := by
  induction fuel generalizing state input encoded updated with
  | zero => simp [literals, fail_run] at success
  | succ fuel induction =>
    rw [literals_run] at success
    cases firstRun : literal fuel state with
    | error error => simp [firstRun, bind, Except.bind] at success
    | ok pair =>
        rcases pair with ⟨first, afterFirst⟩
        simp only [firstRun, bind, Except.bind] at success
        obtain ⟨namedFirst, middle, firstEncoding, firstExtension, firstGrammar, middleClass⟩ :=
          literal_grammar classified firstRun
        split at success
        · cases disjoinRun : expect "|" afterFirst with
          | error error => simp [disjoinRun] at success
          | ok pair =>
              rcases pair with ⟨returnedUnit, afterDisjoin⟩
              cases returnedUnit
              obtain ⟨afterTokens, middleShape, disjoinClass⟩ :=
                expect_punctuation (character := '|') disjoinRun middleClass
                  (by simp [RawPunctuation]) .disjoin .disjoin
              cases tailRun : literals fuel afterDisjoin with
              | error error => simp [disjoinRun, tailRun] at success
              | ok pair =>
                  rcases pair with ⟨tail, final⟩
                  simp [disjoinRun, tailRun, pure, Except.pure] at success
                  rcases success with ⟨rfl, rfl⟩
                  obtain ⟨namedTail, ending, tailEncoding, tailExtension, tailGrammar, finalClass⟩ :=
                    induction disjoinClass tailRun
                  have extension := (expect_tableExtension disjoinRun).trans tailExtension
                  exact ⟨namedFirst :: namedTail, ending,
                    .cons (firstEncoding.extend extension) tailEncoding,
                    firstExtension.trans extension, .more (middleShape ▸ firstGrammar) tailGrammar, finalClass⟩
        · rename_i noDisjoin
          cases success
          have noDisjoinToken : middle.head? ≠ some .disjoin := by
            intro same
            exact noDisjoin (by simpa only [beq_iff_eq] using middleClass.head_disjoin.mpr same)
          exact ⟨[namedFirst], middle, .cons firstEncoding .nil, firstExtension,
            .last firstGrammar noDisjoinToken, middleClass⟩

#print axioms TableClauseEncoding.toSource
#print axioms literals_grammar

end Fang.Frontend
