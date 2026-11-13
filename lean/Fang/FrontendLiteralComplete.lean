/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Construct successful literal and disjunction executions from the independent
grammar and a compatible fixed signature. No parser-success premise is used.
-/
import Fang.FrontendTermComplete
import Fang.FrontendDisjunctionGrammar

namespace Fang.Frontend

open Source.Grammar

theorem function_arguments_complete {input name named rest}
    (parsed : TermTokens (.lower name :: input) (.app name named) rest)
    (signature : Source.Signature) (reserved : State)
    (classified : ClassifiedTokens reserved.tokens input)
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
  | constant name rest noArguments =>
    have noOpen : reserved.tokens.head?.map Token.text ≠ some "(" := by
      intro same
      exact noArguments (classified.head_lparen.mp same)
    exact ⟨0, [], reserved, by simp [noOpen], compatible, .nil, .refl reserved⟩
  | application name children =>
    obtain ⟨opened, openRun, openClass, openExtension, openFunctions, openPredicates⟩ := expect_complete classified
    obtain ⟨fuel, encoded, afterArgs, argsRun, argsCompatible, argsClass, argsEncoding, argsExtension⟩ :=
      arguments_complete children signature opened openClass wellFormed
        (compatible.same_tables openFunctions openPredicates)
    obtain ⟨closed, closeRun, _, closeExtension, closeFunctions, closePredicates⟩ := expect_complete argsClass
    refine ⟨fuel, encoded, closed, ?_, argsCompatible.same_tables closeFunctions closePredicates,
      argsEncoding.extend closeExtension, openExtension.trans (argsExtension.trans closeExtension)⟩
    have hasOpen : reserved.tokens.head?.map Token.text = some "(" := classified.head_lparen.mpr rfl
    change expect "(" reserved = .ok ((), opened) at openRun
    change expect ")" afterArgs = .ok ((), closed) at closeRun
    simp [hasOpen, openRun, argsRun, closeRun, bind, Except.bind, pure, Except.pure]

theorem literal_atom_success {input name named rest state beforeName positive}
    (parsed : TermTokens input (.app name named) rest)
    (signature : Source.Signature) (classified : ClassifiedTokens beforeName.tokens input)
    (wellFormed : Source.TermsWellFormed signature named)
    (declared : signature.predicateArity name = some named.length)
    (compatible : SignatureCompatible signature beforeName)
    (prefixRun : (if state.tokens.head?.map Token.text == some "~" then do
      let (_, updated) ← expect "~" state
      pure (false, updated)
    else .ok (true, state)) = .ok (positive, beforeName)) :
    ∃ fuel encoded updated, literal fuel state = .ok (encoded, updated) ∧
      SignatureCompatible signature updated := by
  have inputShape : ∃ remaining, input = .lower name :: remaining := by
    cases parsed <;> exact ⟨_, rfl⟩
  obtain ⟨remaining, rfl⟩ := inputShape
  obtain ⟨raw, raws, shape, head, tail⟩ := classified.cons_parts
  have valid := head.lower_valid
  obtain ⟨id, reserved, allocated, allocation, consumed, _⟩ :=
    reserveSymbol_spec true raw.text { beforeName with tokens := raws }
  change reserved.tokens = raws at consumed
  have reservedClass : ClassifiedTokens reserved.tokens remaining := consumed ▸ tail
  obtain ⟨fuel, args, afterArgs, argsRun, argsCompatible, argsEncoding, argsExtension⟩ :=
    function_arguments_complete parsed signature reserved reservedClass wellFormed
      (reserveSymbol_compatible (compatible.tokens raws) allocated)
  have reservedId : symbolIndex raw.text reserved.predicates 0 = some id := by
    rw [symbolIndex_eq_namedIndex]
    exact (namedIndex_first_iff _ _ _).mpr allocation.1
  have found := argsExtension.symbols true raw.text id reservedId
  have declared' : signatureArity signature true raw.text = some args.length := by
    simpa only [signatureArity, ↓reduceIte, valid.1, argsEncoding.length] using declared
  obtain ⟨updated, checked, finalCompatible⟩ := checkArity_complete argsCompatible found declared'
    (offset := (beforeName.tokens.head?.map Token.offset).getD beforeName.endOffset)
  refine ⟨fuel, { positive, atom := { pred := id, args } }, updated, ?_, finalCompatible⟩
  rw [literal_run, prefixRun]
  simp only [Except.bind]
  rw [consume_cons beforeName raw raws shape]
  simp only [bind, Except.bind, valid.2.1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, allocated]
  simp only [bind, Except.bind] at argsRun
  rw [argsRun]
  simp [checked, pure, Except.pure]

def LiteralCompletion (signature : Source.Signature) (state : State)
    (named : Source.Literal) (rest : List Source.Grammar.Token) : Prop :=
  ∃ fuel encoded updated, literal fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ ClassifiedTokens updated.tokens rest ∧
    TableLiteralEncoding updated named encoded ∧ TableExtension state updated

theorem literal_complete {input named rest} (parsed : LiteralTokens input named rest)
    (signature : Source.Signature) (state : State)
    (classified : ClassifiedTokens state.tokens input)
    (wellFormed : named.WellFormed signature) (compatible : SignatureCompatible signature state) :
    LiteralCompletion signature state named rest := by
  have runs : ∃ fuel encoded updated, literal fuel state = .ok (encoded, updated) ∧
      SignatureCompatible signature updated := by
    cases parsed with
    | positive atom =>
      have noNegate : state.tokens.head?.map Token.text ≠ some "~" := by
        intro same
        cases atom <;>
          obtain ⟨raw, raws, shape, head, _⟩ := classified.cons_parts <;>
          simp only [shape, List.head?_cons, Option.map_some, Option.some.injEq] at same <;>
          have impossible := head.unique (rawTokenSpelling_punctuation raw '~'
            (by simp [RawPunctuation]) same .negate .negate) <;> cases impossible
      exact literal_atom_success (positive := true) atom signature classified wellFormed.2 wellFormed.1 compatible
        (by simp [noNegate])
    | negative atom =>
      obtain ⟨afterNegate, negateRun, negateClass, _, functions, predicates⟩ := expect_complete classified
      obtain ⟨raw, raws, shape, head, _⟩ := classified.cons_parts
      have hasNegate : state.tokens.head?.map Token.text = some "~" := by
        simpa only [shape, List.head?_cons, Option.map_some, Source.Grammar.Token.text] using congrArg some head.text
      change expect "~" state = .ok ((), afterNegate) at negateRun
      exact literal_atom_success (positive := false) atom signature negateClass wellFormed.2 wellFormed.1
        (compatible.same_tables functions predicates)
        (by simp [hasNegate, negateRun, bind, Except.bind, pure, Except.pure])
  obtain ⟨fuel, encoded, updated, success, finalCompatible⟩ := runs
  obtain ⟨actual, ending, encoding, extension, grammar, remaining⟩ := literal_grammar classified success
  obtain ⟨rfl, rfl⟩ := parsed.unique grammar
  exact ⟨fuel, encoded, updated, success, finalCompatible, remaining, encoding, extension⟩

def DisjunctionCompletion (signature : Source.Signature) (state : State)
    (named : List Source.Literal) (rest : List Source.Grammar.Token) : Prop :=
  ∃ fuel encoded updated, literals fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ ClassifiedTokens updated.tokens (.rparen :: rest) ∧
    TableClauseEncoding updated named encoded ∧ TableExtension state updated

theorem disjunction_complete {input named rest} (parsed : DisjunctionTokens input named rest)
    (signature : Source.Signature) (state : State)
    (classified : ClassifiedTokens state.tokens input)
    (wellFormed : ∀ literal ∈ named, literal.WellFormed signature)
    (compatible : SignatureCompatible signature state) :
    DisjunctionCompletion signature state named rest := by
  induction parsed generalizing state with
  | last head =>
    obtain ⟨fuel, first, final, firstRun, finalCompatible, finalClass, firstEncoding, extension⟩ :=
      literal_complete head signature state classified (wellFormed _ List.mem_cons_self) compatible
    have noDisjoin : final.tokens.head?.map Token.text ≠ some "|" := by
      intro same
      have impossible := finalClass.head_disjoin.mp same
      cases impossible
    refine ⟨fuel + 1, [first], final, ?_, finalCompatible, finalClass,
      .cons firstEncoding .nil, extension⟩
    rw [literals_run]
    simp [firstRun, noDisjoin, bind, Except.bind]
  | more head tail induction =>
    obtain ⟨firstFuel, first, afterFirst, firstRun, firstCompatible, firstClass, firstEncoding, firstExtension⟩ :=
      literal_complete head signature state classified (wellFormed _ List.mem_cons_self) compatible
    obtain ⟨afterDisjoin, disjoinRun, disjoinClass, disjoinExtension, functions, predicates⟩ :=
      expect_complete firstClass
    obtain ⟨tailFuel, args, final, tailRun, finalCompatible, finalClass, tailEncoding, tailExtension⟩ :=
      induction afterDisjoin disjoinClass
        (fun item member => wellFormed item (List.mem_cons_of_mem _ member))
        (firstCompatible.same_tables functions predicates)
    let fuel := max firstFuel tailFuel
    have firstRun' := literal_fuel_monotone firstFuel fuel (Nat.le_max_left _ _) state first afterFirst firstRun
    have tailRun' := literals_fuel_monotone tailFuel fuel (Nat.le_max_right _ _) afterDisjoin args final tailRun
    have hasDisjoin : afterFirst.tokens.head?.map Token.text = some "|" := firstClass.head_disjoin.mpr rfl
    have extension := disjoinExtension.trans tailExtension
    refine ⟨fuel + 1, first :: args, final, ?_, finalCompatible, finalClass,
      .cons (firstEncoding.extend extension) tailEncoding, firstExtension.trans extension⟩
    rw [literals_run]
    change expect "|" afterFirst = .ok ((), afterDisjoin) at disjoinRun
    simp [firstRun', hasDisjoin, disjoinRun, tailRun', bind, Except.bind, pure, Except.pure]

end Fang.Frontend

#print axioms Fang.Frontend.literal_complete
#print axioms Fang.Frontend.disjunction_complete
