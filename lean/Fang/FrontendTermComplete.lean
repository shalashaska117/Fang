/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Converse term and argument parsing for the independent grammar, under a fixed
signature compatible with existing known arities. Fuel is constructed here;
the premise does not assume any successful execution of the parser.
-/
import Fang.FrontendCompatible
import Fang.FrontendFuelBound
import Fang.SourceConsumption

namespace Fang.Frontend

open Source.Grammar

theorem ClassifiedTokens.cons_parts {state : State} {token : Source.Grammar.Token} {rest}
    (classified : ClassifiedTokens state.tokens (token :: rest)) :
    ∃ raw raws, state.tokens = raw :: raws ∧ RawTokenSpelling raw token ∧ ClassifiedTokens raws rest := by
  cases shape : state.tokens with
  | nil => rw [shape] at classified; cases classified
  | cons raw raws =>
    rw [shape] at classified
    cases classified with
    | cons head tail => exact ⟨raw, raws, rfl, head, tail⟩

theorem expect_complete {state : State} {token : Source.Grammar.Token} {rest}
    (classified : ClassifiedTokens state.tokens (token :: rest)) :
    ∃ updated, expect token.text state = .ok ((), updated) ∧
      ClassifiedTokens updated.tokens rest ∧ TableExtension state updated ∧
      updated.functions = state.functions ∧ updated.predicates = state.predicates := by
  obtain ⟨raw, raws, shape, head, tail⟩ := classified.cons_parts
  refine ⟨{ state with tokens := raws }, ?_, tail,
    tableExtension_of_same_tables rfl rfl rfl, rfl, rfl⟩
  rw [← head.text]
  exact expect_cons state raw raws shape

def TermCompletion (signature : Source.Signature) (state : State)
    (named : Source.Term) (rest : List Source.Grammar.Token) : Prop :=
  ∃ fuel encoded updated, term fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ ClassifiedTokens updated.tokens rest ∧
    TableTermEncoding updated named encoded ∧ TableExtension state updated

def ArgumentsCompletion (signature : Source.Signature) (state : State)
    (named : List Source.Term) (rest : List Source.Grammar.Token) : Prop :=
  ∃ fuel encoded updated, terms fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ ClassifiedTokens updated.tokens (.rparen :: rest) ∧
    TableTermsEncoding updated named encoded ∧ TableExtension state updated

theorem termCompletion_of_success {signature state input named rest fuel encoded updated}
    (parsed : TermTokens input named rest) (classified : ClassifiedTokens state.tokens input)
    (success : term fuel state = .ok (encoded, updated))
    (compatible : SignatureCompatible signature updated) :
    TermCompletion signature state named rest := by
  obtain ⟨actual, ending, encoding, extension, grammar, remaining⟩ := term_grammar classified success
  obtain ⟨rfl, rfl⟩ := parsed.unique grammar
  exact ⟨fuel, encoded, updated, success, compatible, remaining, encoding, extension⟩

mutual
theorem term_complete {input named rest} (parsed : TermTokens input named rest)
    (signature : Source.Signature) (state : State)
    (classified : ClassifiedTokens state.tokens input)
    (wellFormed : named.WellFormed signature)
    (compatible : SignatureCompatible signature state) :
    TermCompletion signature state named rest := by
  cases parsed with
  | variableTerm name rest =>
    obtain ⟨raw, raws, shape, head, tail⟩ := classified.cons_parts
    have valid := head.variable_valid
    obtain ⟨id, updated, allocated, _⟩ := variableId_spec raw.text { state with tokens := raws }
    have success : term 1 state = .ok (.var id, updated) := by
      rw [term_variable_run 0 state raw raws shape valid.2]
      simp [allocated, bind, Except.bind, pure, Except.pure]
    exact termCompletion_of_success (.variableTerm name rest) classified success
      (variableId_compatible (compatible.tokens raws) allocated)
  | constant name rest noArguments =>
    obtain ⟨raw, raws, shape, head, tail⟩ := classified.cons_parts
    have valid := head.lower_valid
    have noOpen : raws.head?.map Token.text ≠ some "(" := by
      intro same
      exact noArguments (tail.head_lparen.mp same)
    obtain ⟨id, reserved, allocated, allocation, _, _⟩ :=
      reserveSymbol_spec false raw.text { state with tokens := raws }
    have reservedCompatible := reserveSymbol_compatible (compatible.tokens raws) allocated
    have found : symbolIndex raw.text reserved.functions 0 = some id := by
      rw [symbolIndex_eq_namedIndex]
      exact (namedIndex_first_iff _ _ _).mpr allocation.1
    have declared : signatureArity signature false raw.text = some 0 := by
      simpa only [signatureArity, Bool.false_eq_true, ↓reduceIte, valid.1, List.length_nil] using wellFormed.1
    obtain ⟨updated, checked, finalCompatible⟩ := checkArity_complete reservedCompatible found declared (offset := raw.offset)
    have success : term 1 state = .ok (.app id [], updated) := by
      rw [term_constant_run 0 state raw raws shape valid.2.2 valid.2.1 noOpen]
      simp [allocated, checked, bind, Except.bind, pure, Except.pure]
    exact termCompletion_of_success (.constant name rest noArguments) classified success finalCompatible
  | application name children =>
    obtain ⟨raw, raws, shape, head, tail⟩ := classified.cons_parts
    have valid := head.lower_valid
    obtain ⟨id, reserved, allocated, allocation, consumed, _⟩ :=
      reserveSymbol_spec false raw.text { state with tokens := raws }
    have reservedCompatible := reserveSymbol_compatible (compatible.tokens raws) allocated
    change reserved.tokens = raws at consumed
    have reservedClass : ClassifiedTokens reserved.tokens (.lparen :: _) := consumed ▸ tail
    obtain ⟨opened, openRun, openClass, openExtension, openFunctions, openPredicates⟩ :=
      expect_complete reservedClass
    have openCompatible := reservedCompatible.same_tables openFunctions openPredicates
    obtain ⟨fuel, args, afterArgs, argsRun, argsCompatible, argsClass, argsEncoding, argsExtension⟩ :=
      arguments_complete children signature opened openClass wellFormed.2 openCompatible
    obtain ⟨closed, closeRun, closeClass, closeExtension, closeFunctions, closePredicates⟩ :=
      expect_complete argsClass
    have closedCompatible := argsCompatible.same_tables closeFunctions closePredicates
    have reservedId : symbolIndex raw.text reserved.functions 0 = some id := by
      rw [symbolIndex_eq_namedIndex]
      exact (namedIndex_first_iff _ _ _).mpr allocation.1
    have found := (openExtension.trans (argsExtension.trans closeExtension)).symbols false raw.text id reservedId
    have declared : signatureArity signature false raw.text = some args.length := by
      simpa only [signatureArity, Bool.false_eq_true, ↓reduceIte, valid.1, argsEncoding.length] using wellFormed.1
    obtain ⟨updated, checked, finalCompatible⟩ := checkArity_complete closedCompatible found declared (offset := raw.offset)
    have hasOpen : raws.head?.map Token.text = some "(" := tail.head_lparen.mpr rfl
    have success : term (fuel + 1) state = .ok (.app id args, updated) := by
      rw [term_function_run fuel state reserved raw raws id shape valid.2.2 valid.2.1 allocated consumed]
      simp only [hasOpen, beq_self_eq_true, ↓reduceIte]
      change expect "(" reserved = .ok ((), opened) at openRun
      change expect ")" afterArgs = .ok ((), closed) at closeRun
      simp [openRun, argsRun, closeRun, checked, bind, Except.bind, pure, Except.pure]
    exact termCompletion_of_success (.application name children) classified success finalCompatible
termination_by 2 * input.length
decreasing_by simp_wf; subst input; simp only [List.length_cons]; omega

theorem arguments_complete {input named rest} (parsed : ArgumentsTokens input named rest)
    (signature : Source.Signature) (state : State)
    (classified : ClassifiedTokens state.tokens input)
    (wellFormed : Source.TermsWellFormed signature named)
    (compatible : SignatureCompatible signature state) :
    ArgumentsCompletion signature state named rest := by
  cases parsed with
  | last head =>
    obtain ⟨fuel, first, final, firstRun, finalCompatible, finalClass, firstEncoding, extension⟩ :=
      term_complete head signature state classified wellFormed.1 compatible
    have noComma : final.tokens.head?.map Token.text ≠ some "," := by
      intro same
      have impossible := finalClass.head_comma.mp same
      cases impossible
    refine ⟨fuel + 1, [first], final, ?_, finalCompatible, finalClass,
      .cons firstEncoding .nil, extension⟩
    rw [terms_run]
    simp [firstRun, noComma, bind, Except.bind]
  | more head tail =>
    obtain ⟨firstFuel, first, afterFirst, firstRun, firstCompatible, firstClass, firstEncoding, firstExtension⟩ :=
      term_complete head signature state classified wellFormed.1 compatible
    obtain ⟨afterComma, commaRun, commaClass, commaExtension, commaFunctions, commaPredicates⟩ :=
      expect_complete firstClass
    have commaCompatible := firstCompatible.same_tables commaFunctions commaPredicates
    obtain ⟨tailFuel, args, final, tailRun, finalCompatible, finalClass, tailEncoding, tailExtension⟩ :=
      arguments_complete tail signature afterComma commaClass wellFormed.2 commaCompatible
    let fuel := max firstFuel tailFuel
    have firstRun' := term_fuel_monotone firstFuel fuel (Nat.le_max_left _ _) state first afterFirst firstRun
    have tailRun' := terms_fuel_monotone tailFuel fuel (Nat.le_max_right _ _) afterComma args final tailRun
    have hasComma : afterFirst.tokens.head?.map Token.text = some "," := firstClass.head_comma.mpr rfl
    have extension := commaExtension.trans tailExtension
    refine ⟨fuel + 1, first :: args, final, ?_, finalCompatible, finalClass,
      .cons (firstEncoding.extend extension) tailEncoding, firstExtension.trans extension⟩
    rw [terms_run]
    change expect "," afterFirst = .ok ((), afterComma) at commaRun
    simp [firstRun', hasComma, commaRun, tailRun', bind, Except.bind, pure, Except.pure]
termination_by 2 * input.length + 1
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have smaller := head.consumes; simp at smaller; omega
end

theorem term_complete_token_count {input named rest} (parsed : TermTokens input named rest)
    (signature : Source.Signature) (state : State)
    (classified : ClassifiedTokens state.tokens input)
    (wellFormed : named.WellFormed signature) (compatible : SignatureCompatible signature state) :
    ∃ encoded updated, term state.tokens.length state = .ok (encoded, updated) ∧
      SignatureCompatible signature updated ∧ ClassifiedTokens updated.tokens rest ∧
      TableTermEncoding updated named encoded ∧ TableExtension state updated := by
  obtain ⟨fuel, encoded, updated, success, facts⟩ :=
    term_complete parsed signature state classified wellFormed compatible
  exact ⟨encoded, updated, term_fuel_sufficient fuel state.tokens.length state encoded updated
    (by omega) success, facts⟩

end Fang.Frontend

#print axioms Fang.Frontend.term_complete
#print axioms Fang.Frontend.arguments_complete
#print axioms Fang.Frontend.term_complete_token_count
