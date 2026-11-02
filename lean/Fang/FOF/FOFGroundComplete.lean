/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Fang.FOF.FOFFormulaComplete
import Fang.FrontendStatementComplete

namespace Fang.FOFFrontend
open Frontend FOFGrammar

def RawDeclarationCompletion (signature : Source.Signature) (state : State)
    (named : NamedFOF.Declaration) (rest : List String) : Prop :=
  ∃ fuel encoded updated, statement fuel state = .ok (encoded, updated) ∧
    SignatureCompatible signature updated ∧ spellings updated = rest ∧
    TableDeclarationEncoding updated named encoded ∧ SymbolExtension state updated ∧
    updated.clauseNames = state.clauseNames ++ [named.name]

def GroundTailRun (fuel : Nat) (state : State) (body : GroundFOF.Formula) (final : State) : Prop :=
  ((do
    expect ","
    if (← peek) != some "axiom" then fail "unsupported: only the axiom role is supported"
    expect "axiom"
    expect ","
    let body ← formula fuel
    if !groundFormula body then fail "invalid-syntax: free FOF variable"
    if (← peek) == some "," then fail "unsupported: TPTP annotations"
    expect ")"
    expect "."
    pure (.fof body) : Parser GroundFOF.Declaration) state) = .ok (.fof body, final)

theorem raw_ground_tail_complete {input named rest}
    (parsed : FormulaTokens input named (")" :: "." :: rest))
    (signature : Source.Signature) (state : State)
    (words : spellings state = "," :: "axiom" :: "," :: input)
    (wellFormed : named.WellFormed signature) (ground : named.Ground)
    (compatible : SignatureCompatible signature state) :
    ∃ fuel encoded updated, GroundTailRun fuel state encoded updated ∧
      SignatureCompatible signature updated := by
  obtain ⟨afterComma, commaRun, commaWords, _, commaFunctions, commaPredicates⟩ := raw_expect_complete words
  obtain ⟨afterRole, roleRun, roleWords, _, roleFunctions, rolePredicates⟩ := raw_expect_complete commaWords
  obtain ⟨beforeBody, nextRun, bodyWords, _, nextFunctions, nextPredicates⟩ := raw_expect_complete roleWords
  have bodyCompatible := ((compatible.same_tables commaFunctions commaPredicates).same_tables
    roleFunctions rolePredicates).same_tables nextFunctions nextPredicates
  obtain ⟨fuel, encoded, afterBody, bodyRun, afterCompatible, closingWords, encoding, _⟩ :=
    raw_formula_complete parsed signature beforeBody bodyWords wellFormed bodyCompatible
  obtain ⟨closed, closing, periodWords, _, closeFunctions, closePredicates⟩ := raw_expect_complete closingWords
  obtain ⟨updated, period, _, _, finalFunctions, finalPredicates⟩ := raw_expect_complete periodWords
  have groundBool : groundFormula encoded = true := (groundFormula_correct encoded).mpr
    (encoding.ground_iff.mpr ground)
  have roleHead : afterComma.tokens.head?.map Token.text = some "axiom" := by
    rw [← spellings_head, commaWords]; rfl
  have closeHead : afterBody.tokens.head?.map Token.text = some ")" := by
    rw [← spellings_head, closingWords]; rfl
  refine ⟨fuel, encoded, updated, ?_, (afterCompatible.same_tables closeFunctions closePredicates).same_tables
    finalFunctions finalPredicates⟩
  simp [GroundTailRun, bind, StateT.bind, commaRun, peek_run, roleHead, roleRun, nextRun,
    bodyRun, groundBool, closeHead, closing, period, Except.bind, pure, StateT.pure, Except.pure]

theorem ground_statement_success_of_parts {fuel state afterFof opened namedState final body name}
    (head : state.tokens.head?.map Token.text = some "fof")
    (fofRun : expect "fof" state = .ok ((), afterFof))
    (openRun : expect "(" afterFof = .ok ((), opened))
    (nameRun : consume opened = .ok (name, namedState))
    (valid : lowerName name = true) (fresh : name ∉ namedState.clauseNames)
    (tailRun : GroundTailRun fuel
      { namedState with clauseNames := namedState.clauseNames ++ [name], variables := [] } body final) :
    statement fuel state = .ok (.fof body, final) := by
  have wrongKind : ((some "fof" : Option String) == some "cnf") = false := rfl
  unfold Fang.FOFFrontend.statement
  simp only [bind, StateT.bind, peek_run, head, wrongKind, beq_self_eq_true, ↓reduceIte,
    fofRun, openRun, position_run, nameRun, valid, Bool.not_true, Bool.false_eq_true,
    pure, Except.bind]
  simpa only [GroundTailRun, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    List.contains_eq_mem, fresh, decide_false, Bool.false_eq_true, ↓reduceIte, set, StateT.set,
    Except.bind, pure, StateT.pure, Except.pure] using tailRun

theorem raw_ground_statement_complete {input name named rest}
    (parsed : GroundDeclarationTokens input name named rest)
    (signature : Source.Signature) (state : State) (words : spellings state = input)
    (wellFormed : named.WellFormed signature) (compatible : SignatureCompatible signature state)
    (fresh : name ∉ state.clauseNames) :
    RawDeclarationCompletion signature state (.fof name named) rest := by
  have runs : ∃ fuel encoded updated, statement fuel state = .ok (.fof encoded, updated) ∧
      SignatureCompatible signature updated := by
    cases parsed with
    | «axiom» valid body ground =>
      have head : state.tokens.head?.map Token.text = some "fof" := by rw [← spellings_head, words]; rfl
      obtain ⟨afterFof, fofRun, fofWords, _, fofFunctions, fofPredicates⟩ := raw_expect_complete words
      obtain ⟨opened, openRun, openWords, _, openFunctions, openPredicates⟩ := raw_expect_complete fofWords
      obtain ⟨raw, raws, shape, text, tail⟩ := spellings_cons_parts openWords
      let namedState : State := { opened with tokens := raws }
      let reset : State := { namedState with clauseNames := namedState.clauseNames ++ [name], variables := [] }
      have resetWords : spellings reset = _ := tail
      have resetCompatible : SignatureCompatible signature reset :=
        (compatible.same_tables fofFunctions fofPredicates).same_tables openFunctions openPredicates
      obtain ⟨fuel, encoded, updated, tailRun, finalCompatible⟩ :=
        raw_ground_tail_complete body signature reset resetWords wellFormed ground resetCompatible
      have names : namedState.clauseNames = state.clauseNames := by
        dsimp [namedState]
        exact (expect_clause_names openRun).trans (expect_clause_names fofRun)
      have nameRun : consume opened = .ok (name, namedState) := by
        simpa only [text] using consume_cons opened raw raws shape
      exact ⟨fuel, encoded, updated, ground_statement_success_of_parts head fofRun openRun nameRun
        (raw_lower_valid valid).1 (by simpa only [names] using fresh) tailRun, finalCompatible⟩
  obtain ⟨fuel, encoded, updated, success, finalCompatible⟩ := runs
  have notCnf : (state.tokens.head?.map Token.text == some "cnf") ≠ true := by
    cases parsed
    rw [← spellings_head, words]
    simp
  obtain ⟨actualName, actual, encoding, extension, _, names, grammar⟩ :=
    raw_ground_statement_grammar notCnf success
  rw [words] at grammar
  obtain ⟨rfl, rfl, restEqual⟩ := parsed.unique grammar
  exact ⟨fuel, .fof encoded, updated, success, finalCompatible, restEqual.symm, encoding,
    extension, names⟩

end Fang.FOFFrontend
