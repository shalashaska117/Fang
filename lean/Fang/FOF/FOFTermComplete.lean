/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFCNFUniqueness
import Fang.FrontendTermComplete

namespace Fang.FOFGrammar

theorem TermTokens.consumes {input named rest} (parsed : TermTokens input named rest) :
    rest.length < input.length := by
  obtain ⟨front, nonempty, rfl⟩ := parsed.suffix
  have positive : 0 < front.length := List.length_pos_iff.mpr nonempty
  simp only [List.length_append]
  omega

end Fang.FOFGrammar

namespace Fang.FOFFrontend
open Frontend FOFGrammar

theorem raw_lower_valid {name} (valid : Source.Grammar.LowerName name) :
    lowerName name = true ∧ variableName name = false := by
  have spelling : RawTokenSpelling { text := name, offset := 0 } (.lower name) :=
    Or.inl (.lower name rfl valid)
  exact spelling.lower_valid.2

theorem raw_variable_valid {name} (valid : Source.Grammar.VariableName name) :
    variableName name = true := by
  have spelling : RawTokenSpelling { text := name, offset := 0 } (.variable name) :=
    Or.inl (.variableWord name rfl valid)
  exact spelling.variable_valid.2

theorem spellings_cons_parts {state : State} {name rest}
    (words : spellings state = name :: rest) :
    ∃ raw raws, state.tokens = raw :: raws ∧ raw.text = name ∧ raws.map Token.text = rest := by
  cases tokens : state.tokens with
  | nil => simp [spellings, tokens] at words
  | cons raw raws =>
    have parts : raw.text = name ∧ raws.map Token.text = rest := by
      simpa only [spellings, tokens, List.map_cons, List.cons.injEq] using words
    exact ⟨raw, raws, rfl, parts⟩

theorem raw_expect_complete {state : State} {name rest}
    (words : spellings state = name :: rest) :
    ∃ updated, expect name state = .ok ((), updated) ∧ spellings updated = rest ∧
      TableExtension state updated ∧ updated.functions = state.functions ∧
      updated.predicates = state.predicates := by
  obtain ⟨raw, raws, shape, text, tail⟩ := spellings_cons_parts words
  refine ⟨{state with tokens := raws}, ?_, tail,
    tableExtension_of_same_tables rfl rfl rfl, rfl, rfl⟩
  rw [← text]
  exact expect_cons state raw raws shape

def RawTermCompletion (signature : Source.Signature) (state : State)
    (named : Source.Term) (rest : List String) : Prop :=
  ∃ fuel encoded updated, term fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ spellings updated = rest ∧
    TableTermEncoding updated named encoded ∧ TableExtension state updated

def RawArgumentsCompletion (signature : Source.Signature) (state : State)
    (named : List Source.Term) (rest : List String) : Prop :=
  ∃ fuel encoded updated, terms fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ spellings updated = ")" :: rest ∧
    TableTermsEncoding updated named encoded ∧ TableExtension state updated

theorem raw_termCompletion_of_success {signature state input named rest fuel encoded updated}
    (parsed : FOFGrammar.TermTokens input named rest) (words : spellings state = input)
    (success : term fuel state = .ok (encoded, updated))
    (compatible : SignatureCompatible signature updated) :
    RawTermCompletion signature state named rest := by
  obtain ⟨actual, encoding, extension, grammar⟩ := raw_term_grammar success
  rw [words] at grammar
  obtain ⟨rfl, equal⟩ := parsed.unique grammar
  exact ⟨fuel, encoded, updated, success, compatible, equal.symm, encoding, extension⟩

mutual
theorem raw_term_complete {input named rest} (parsed : FOFGrammar.TermTokens input named rest)
    (signature : Source.Signature) (state : State) (words : spellings state = input)
    (wellFormed : named.WellFormed signature) (compatible : SignatureCompatible signature state) :
    RawTermCompletion signature state named rest := by
  cases parsed with
  | variableTerm name rest valid =>
    obtain ⟨raw, raws, shape, text, tail⟩ := spellings_cons_parts words
    have validBool : variableName raw.text = true := text ▸ raw_variable_valid valid
    obtain ⟨id, updated, allocated, _⟩ := variableId_spec raw.text { state with tokens := raws }
    have success : term 1 state = .ok (.var id, updated) := by
      rw [term_variable_run 0 state raw raws shape validBool]
      simp [allocated, bind, Except.bind, pure, Except.pure]
    exact raw_termCompletion_of_success (.variableTerm name rest valid) words success
      (variableId_compatible (compatible.tokens raws) allocated)
  | constant name rest valid noArguments =>
    obtain ⟨raw, raws, shape, text, tail⟩ := spellings_cons_parts words
    have validBool : lowerName raw.text = true ∧ variableName raw.text = false :=
      text ▸ raw_lower_valid valid
    have noOpen : raws.head?.map Token.text ≠ some "(" := by
      intro same
      have head : (raws.map Token.text).head? = some "(" := by simpa using same
      rw [tail] at head
      exact noArguments head
    obtain ⟨id, reserved, allocated, allocation, _, _⟩ :=
      reserveSymbol_spec false raw.text { state with tokens := raws }
    have reservedCompatible := reserveSymbol_compatible (compatible.tokens raws) allocated
    have found : symbolIndex raw.text reserved.functions 0 = some id := by
      rw [symbolIndex_eq_namedIndex]
      exact (namedIndex_first_iff _ _ _).mpr allocation.1
    have declared : signatureArity signature false raw.text = some 0 := by
      simpa only [signatureArity, Bool.false_eq_true, ↓reduceIte, text, List.length_nil] using wellFormed.1
    obtain ⟨updated, checked, finalCompatible⟩ := checkArity_complete reservedCompatible found declared (offset := raw.offset)
    have success : term 1 state = .ok (.app id [], updated) := by
      rw [term_constant_run 0 state raw raws shape validBool.2 validBool.1 noOpen]
      simp [allocated, checked, bind, Except.bind, pure, Except.pure]
    exact raw_termCompletion_of_success (.constant name rest valid noArguments) words success finalCompatible
  | application name valid children =>
    obtain ⟨raw, raws, shape, text, tail⟩ := spellings_cons_parts words
    have validBool : lowerName raw.text = true ∧ variableName raw.text = false :=
      text ▸ raw_lower_valid valid
    obtain ⟨id, reserved, allocated, allocation, consumed, _⟩ :=
      reserveSymbol_spec false raw.text { state with tokens := raws }
    have reservedCompatible := reserveSymbol_compatible (compatible.tokens raws) allocated
    change reserved.tokens = raws at consumed
    have reservedWords := congrArg (List.map Token.text) consumed
    change spellings reserved = raws.map Token.text at reservedWords
    rw [tail] at reservedWords
    obtain ⟨opened, openRun, openWords, openExtension, openFunctions, openPredicates⟩ :=
      raw_expect_complete reservedWords
    have openCompatible := reservedCompatible.same_tables openFunctions openPredicates
    obtain ⟨fuel, args, afterArgs, argsRun, argsCompatible, argsWords, argsEncoding, argsExtension⟩ :=
      raw_arguments_complete children signature opened openWords wellFormed.2 openCompatible
    obtain ⟨closed, closeRun, closeWords, closeExtension, closeFunctions, closePredicates⟩ :=
      raw_expect_complete argsWords
    have closedCompatible := argsCompatible.same_tables closeFunctions closePredicates
    have reservedId : symbolIndex raw.text reserved.functions 0 = some id := by
      rw [symbolIndex_eq_namedIndex]
      exact (namedIndex_first_iff _ _ _).mpr allocation.1
    have found := (openExtension.trans (argsExtension.trans closeExtension)).symbols false raw.text id reservedId
    have declared : signatureArity signature false raw.text = some args.length := by
      simpa only [signatureArity, Bool.false_eq_true, ↓reduceIte, text, argsEncoding.length] using wellFormed.1
    obtain ⟨updated, checked, finalCompatible⟩ := checkArity_complete closedCompatible found declared (offset := raw.offset)
    have hasOpen : raws.head?.map Token.text = some "(" := by
      have equal := congrArg List.head? tail
      simpa using equal
    have success : term (fuel + 1) state = .ok (.app id args, updated) := by
      rw [term_function_run fuel state reserved raw raws id shape validBool.2 validBool.1 allocated consumed]
      simp only [hasOpen, beq_self_eq_true, ↓reduceIte]
      simp [openRun, argsRun, closeRun, checked, bind, Except.bind, pure, Except.pure]
    exact raw_termCompletion_of_success (.application name valid children) words success finalCompatible
termination_by 2 * input.length
decreasing_by
  simp_wf
  have lengths := congrArg List.length words
  simp only [List.length_cons] at lengths
  subst input
  omega

theorem raw_arguments_complete {input named rest} (parsed : FOFGrammar.ArgumentsTokens input named rest)
    (signature : Source.Signature) (state : State) (words : spellings state = input)
    (wellFormed : Source.TermsWellFormed signature named) (compatible : SignatureCompatible signature state) :
    RawArgumentsCompletion signature state named rest := by
  cases parsed with
  | last head =>
    obtain ⟨fuel, first, final, firstRun, finalCompatible, finalWords, firstEncoding, extension⟩ :=
      raw_term_complete head signature state words wellFormed.1 compatible
    have noComma : final.tokens.head?.map Token.text ≠ some "," := by
      rw [← spellings_head, finalWords]
      simp
    refine ⟨fuel + 1, [first], final, ?_, finalCompatible, finalWords,
      .cons firstEncoding .nil, extension⟩
    rw [terms_run]
    simp [firstRun, noComma, bind, Except.bind]
  | more head tail =>
    obtain ⟨firstFuel, first, afterFirst, firstRun, firstCompatible, firstWords, firstEncoding, firstExtension⟩ :=
      raw_term_complete head signature state words wellFormed.1 compatible
    obtain ⟨afterComma, commaRun, commaWords, commaExtension, commaFunctions, commaPredicates⟩ :=
      raw_expect_complete firstWords
    have commaCompatible := firstCompatible.same_tables commaFunctions commaPredicates
    obtain ⟨tailFuel, args, final, tailRun, finalCompatible, finalWords, tailEncoding, tailExtension⟩ :=
      raw_arguments_complete tail signature afterComma commaWords wellFormed.2 commaCompatible
    let fuel := max firstFuel tailFuel
    have firstRun' := term_fuel_monotone firstFuel fuel (Nat.le_max_left _ _) state first afterFirst firstRun
    have tailRun' := terms_fuel_monotone tailFuel fuel (Nat.le_max_right _ _) afterComma args final tailRun
    have hasComma : afterFirst.tokens.head?.map Token.text = some "," := by
      rw [← spellings_head, firstWords]
      rfl
    have extension := commaExtension.trans tailExtension
    refine ⟨fuel + 1, first :: args, final, ?_, finalCompatible, finalWords,
      .cons (firstEncoding.extend extension) tailEncoding, firstExtension.trans extension⟩
    rw [terms_run]
    simp [firstRun', hasComma, commaRun, tailRun', bind, Except.bind, pure, Except.pure]
termination_by 2 * input.length + 1
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have smaller := head.consumes; simp at smaller; omega
end

theorem raw_term_complete_token_count {input named rest}
    (parsed : FOFGrammar.TermTokens input named rest) (signature : Source.Signature) (state : State)
    (words : spellings state = input) (wellFormed : named.WellFormed signature)
    (compatible : SignatureCompatible signature state) :
    ∃ encoded updated, term state.tokens.length state = .ok (encoded, updated) ∧
      SignatureCompatible signature updated ∧ spellings updated = rest ∧
      TableTermEncoding updated named encoded ∧ TableExtension state updated := by
  obtain ⟨fuel, encoded, updated, success, facts⟩ := raw_term_complete parsed signature state words wellFormed compatible
  exact ⟨encoded, updated, term_fuel_sufficient fuel state.tokens.length state encoded updated (by omega) success, facts⟩

end Fang.FOFFrontend
