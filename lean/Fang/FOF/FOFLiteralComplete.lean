/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFTermComplete

namespace Fang.FOFFrontend
open Frontend FOFGrammar

theorem raw_function_arguments_complete {input name named rest}
    (parsed : TermTokens (name :: input) (.app name named) rest)
    (signature : Source.Signature) (reserved : State) (words : spellings reserved = input)
    (wellFormed : Source.TermsWellFormed signature named)
    (compatible : SignatureCompatible signature reserved) :
    ∃ fuel encoded updated,
      (if reserved.tokens.head?.map Token.text == some "(" then do
        let (_, opened) ← expect "(" reserved
        let (args, afterArgs) ← terms fuel opened
        let (_, closed) ← expect ")" afterArgs
        pure (args, closed)
      else .ok ([], reserved)) = .ok (encoded, updated) ∧
      SignatureCompatible signature updated ∧ TableTermsEncoding updated named encoded ∧
      TableExtension reserved updated := by
  cases parsed with
  | constant name rest valid noArguments =>
    have noOpen : reserved.tokens.head?.map Token.text ≠ some "(" := by
      rw [← spellings_head, words]
      exact noArguments
    exact ⟨0, [], reserved, by simp [noOpen], compatible, .nil, .refl reserved⟩
  | application name valid children =>
    obtain ⟨opened, openRun, openWords, openExtension, openFunctions, openPredicates⟩ := raw_expect_complete words
    obtain ⟨fuel, encoded, afterArgs, argsRun, argsCompatible, argsWords, argsEncoding, argsExtension⟩ :=
      raw_arguments_complete children signature opened openWords wellFormed
        (compatible.same_tables openFunctions openPredicates)
    obtain ⟨closed, closeRun, _, closeExtension, closeFunctions, closePredicates⟩ := raw_expect_complete argsWords
    refine ⟨fuel, encoded, closed, ?_, argsCompatible.same_tables closeFunctions closePredicates,
      argsEncoding.extend closeExtension, openExtension.trans (argsExtension.trans closeExtension)⟩
    have hasOpen : reserved.tokens.head?.map Token.text = some "(" := by
      rw [← spellings_head, words]
      rfl
    simp [hasOpen, openRun, argsRun, closeRun, bind, Except.bind, pure, Except.pure]

theorem raw_literal_atom_success {input name named rest state beforeName positive}
    (parsed : TermTokens input (.app name named) rest)
    (signature : Source.Signature) (words : spellings beforeName = input)
    (wellFormed : Source.TermsWellFormed signature named)
    (declared : signature.predicateArity name = some named.length)
    (compatible : SignatureCompatible signature beforeName)
    (prefixRun : (if state.tokens.head?.map Token.text == some "~" then do
      let (_, updated) ← expect "~" state
      pure (false, updated)
    else .ok (true, state)) = .ok (positive, beforeName)) :
    ∃ fuel encoded updated, literal fuel state = .ok (encoded, updated) ∧
      SignatureCompatible signature updated := by
  obtain ⟨remaining, inputShape, valid⟩ := parsed.app_head
  have words' := words.trans inputShape
  have parsed' := inputShape ▸ parsed
  obtain ⟨raw, raws, shape, text, tail⟩ := spellings_cons_parts words'
  have validBool : lowerName raw.text = true := by simpa only [text] using (raw_lower_valid valid).1
  obtain ⟨id, reserved, allocated, allocation, consumed, _⟩ :=
    reserveSymbol_spec true raw.text { beforeName with tokens := raws }
  change reserved.tokens = raws at consumed
  have reservedWords : spellings reserved = remaining := by simpa only [spellings, consumed] using tail
  obtain ⟨fuel, args, afterArgs, argsRun, argsCompatible, argsEncoding, argsExtension⟩ :=
    raw_function_arguments_complete parsed' signature reserved reservedWords wellFormed
      (reserveSymbol_compatible (compatible.tokens raws) allocated)
  have reservedId : symbolIndex raw.text reserved.predicates 0 = some id := by
    rw [symbolIndex_eq_namedIndex]
    exact (namedIndex_first_iff _ _ _).mpr allocation.1
  have found := argsExtension.symbols true raw.text id reservedId
  have declared' : signatureArity signature true raw.text = some args.length := by
    simpa only [signatureArity, ↓reduceIte, text, argsEncoding.length] using declared
  obtain ⟨updated, checked, finalCompatible⟩ := checkArity_complete argsCompatible found declared'
    (offset := (beforeName.tokens.head?.map Token.offset).getD beforeName.endOffset)
  refine ⟨fuel, { positive, atom := { pred := id, args } }, updated, ?_, finalCompatible⟩
  rw [literal_run, prefixRun]
  simp only [Except.bind]
  rw [consume_cons beforeName raw raws shape]
  simp only [bind, Except.bind, validBool, Bool.not_true, Bool.false_eq_true, ↓reduceIte, allocated]
  simp only [bind, Except.bind] at argsRun
  rw [argsRun]
  simp [checked, pure, Except.pure]

def RawLiteralCompletion (signature : Source.Signature) (state : State)
    (named : Source.Literal) (rest : List String) : Prop :=
  ∃ fuel encoded updated, literal fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ spellings updated = rest ∧
    TableLiteralEncoding updated named encoded ∧ TableExtension state updated

theorem raw_literal_complete {input named rest} (parsed : LiteralTokens input named rest)
    (signature : Source.Signature) (state : State) (words : spellings state = input)
    (wellFormed : named.WellFormed signature) (compatible : SignatureCompatible signature state) :
    RawLiteralCompletion signature state named rest := by
  have runs : ∃ fuel encoded updated, literal fuel state = .ok (encoded, updated) ∧
      SignatureCompatible signature updated := by
    cases parsed with
    | positive atom =>
      have noNegate : state.tokens.head?.map Token.text ≠ some "~" := by
        rw [← spellings_head, words]
        exact atom.app_not_head negate_not_lower
      exact raw_literal_atom_success (positive := true) atom signature words wellFormed.2 wellFormed.1 compatible
        (by simp [noNegate])
    | negative atom =>
      obtain ⟨afterNegate, negateRun, negateWords, _, functions, predicates⟩ := raw_expect_complete words
      have hasNegate : state.tokens.head?.map Token.text = some "~" := by
        rw [← spellings_head, words]
        rfl
      exact raw_literal_atom_success (positive := false) atom signature negateWords wellFormed.2 wellFormed.1
        (compatible.same_tables functions predicates)
        (by simp [hasNegate, negateRun, bind, Except.bind, pure, Except.pure])
  obtain ⟨fuel, encoded, updated, success, finalCompatible⟩ := runs
  obtain ⟨actual, encoding, extension, grammar⟩ := raw_literal_grammar success
  rw [words] at grammar
  obtain ⟨rfl, restEqual⟩ := parsed.unique grammar
  exact ⟨fuel, encoded, updated, success, finalCompatible, restEqual.symm, encoding, extension⟩

end Fang.FOFFrontend
