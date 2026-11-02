/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Checked numeric-to-named construction for the independent Lean exporter.
   Supplied tables are checked at each represented occurrence. -/
import QuantifiedBytes
import QuantifiedTableEncoding
import Fang.FrontendTokenView

namespace Fang.QuantifiedTstp.Naming
open Frontend Source.Grammar QuantifiedFrontend

def variableAt (state : State) (id : Nat) : Except String String := do
  let some name := state.variables[id]? | .error "export-error: missing variable"
  if !variableName name then .error "export-error: invalid variable spelling"
  if namedIndex name state.variables 0 != some id then
    .error "export-error: ambiguous variable index"
  pure name

def symbol (symbols : List Symbol) (id arity : Nat) : Except String String := do
  let some entry := symbols[id]? | .error "export-error: missing symbol"
  if !lowerName entry.name then .error "export-error: invalid symbol spelling"
  if entry.arity != some arity then .error "export-error: symbol arity mismatch"
  if symbolIndex entry.name symbols 0 != some id then
    .error "export-error: ambiguous symbol index"
  pure entry.name

mutual
def reifyTerm (state : State) : Fang.Term → Except String Source.Term
  | .var id => do pure (.var (← variableAt state id))
  | .app id args => do
    let name ← symbol state.functions id args.length
    pure (.app name (← reifyTerms state args))

def reifyTerms (state : State) : List Fang.Term → Except String (List Source.Term)
  | [] => pure []
  | first :: rest => do
    pure ((← reifyTerm state first) :: (← reifyTerms state rest))
end

def reifyFormula (state : State) : QuantifiedFOF.Formula → Except String NamedQuantified.Formula
  | .atom atom => do
    let name ← symbol state.predicates atom.pred atom.args.length
    pure (.atom name (← reifyTerms state atom.args))
  | .truth => pure .truth
  | .falsity => pure .falsity
  | .neg body => do pure (.neg (← reifyFormula state body))
  | .conj left right => do pure (.conj (← reifyFormula state left) (← reifyFormula state right))
  | .disj left right => do pure (.disj (← reifyFormula state left) (← reifyFormula state right))
  | .implies left right => do pure (.implies (← reifyFormula state left) (← reifyFormula state right))
  | .all id body => do pure (.all (← variableAt state id) (← reifyFormula state body))
  | .ex id body => do pure (.ex (← variableAt state id) (← reifyFormula state body))

theorem variableAt_correct {state id name} (success : variableAt state id = .ok name) :
    VariableName name ∧ namedIndex name state.variables 0 = some id := by
  cases found : state.variables[id]? with
  | none => simp [variableAt, found] at success
  | some value =>
    by_cases valid : variableName value = true
    · by_cases same : namedIndex value state.variables 0 = some id
      · simp [variableAt, found, valid, same, pure, Except.pure] at success
        subst name
        exact ⟨(variableName_iff value (variableName_ascii valid)).mp valid, same⟩
      · simp [variableAt, found, valid, same, bind, Except.bind] at success
    · simp [variableAt, found, valid, bind, Except.bind] at success

theorem symbol_correct {symbols id arity name} (success : symbol symbols id arity = .ok name) :
    LowerName name ∧ symbolIndex name symbols 0 = some id ∧
      (symbols[id]?).map Symbol.arity = some (some arity) := by
  cases found : symbols[id]? with
  | none => simp [symbol, found] at success
  | some entry =>
    by_cases valid : lowerName entry.name = true
    · by_cases correctArity : entry.arity = some arity
      · by_cases same : symbolIndex entry.name symbols 0 = some id
        · simp [symbol, found, valid, correctArity, same, pure, Except.pure] at success
          subst name
          exact ⟨(lowerName_iff entry.name (lowerName_ascii valid)).mp valid,
            same, by simp [correctArity]⟩
        · simp [symbol, found, valid, correctArity, same, bind, Except.bind] at success
      · simp [symbol, found, valid, correctArity, bind, Except.bind] at success
    · simp [symbol, found, valid, bind, Except.bind] at success

mutual
theorem reifyTerm_correct (state : State) (value : Fang.Term) {named}
    (success : reifyTerm state value = .ok named) :
    TableTermEncoding state named value ∧ Tokens.TermNames named := by
  cases value with
  | var id =>
    cases called : variableAt state id with
    | error error => simp [reifyTerm, called, bind, Except.bind] at success
    | ok name =>
      simp [reifyTerm, called, bind, Except.bind, pure, Except.pure] at success
      subst named
      obtain ⟨valid, found⟩ := variableAt_correct called
      exact ⟨.var name id found, by simpa [Tokens.TermNames] using valid⟩
  | app id args =>
    cases called : symbol state.functions id args.length with
    | error error => simp [reifyTerm, called, bind, Except.bind] at success
    | ok name =>
      cases children : reifyTerms state args with
      | error error => simp [reifyTerm, called, children, bind, Except.bind] at success
      | ok names =>
        simp [reifyTerm, called, children, bind, Except.bind, pure, Except.pure] at success
        subst named
        obtain ⟨valid, found, arity⟩ := symbol_correct called
        obtain ⟨encoded, validTerms⟩ := reifyTerms_correct state args children
        rw [← encoded.length] at arity
        exact ⟨.app name id names args found arity encoded, by simpa [Tokens.TermNames] using And.intro valid validTerms⟩
termination_by sizeOf value

theorem reifyTerms_correct (state : State) (values : List Fang.Term) {named}
    (success : reifyTerms state values = .ok named) :
    TableTermsEncoding state named values ∧ ∀ term ∈ named, Tokens.TermNames term := by
  cases values with
  | nil =>
    simp [reifyTerms, pure, Except.pure] at success
    subst named
    exact ⟨.nil, by simp⟩
  | cons first rest =>
    cases called : reifyTerm state first with
    | error error => simp [reifyTerms, called, bind, Except.bind] at success
    | ok name =>
      cases children : reifyTerms state rest with
      | error error => simp [reifyTerms, called, children, bind, Except.bind] at success
      | ok names =>
        simp [reifyTerms, called, children, bind, Except.bind, pure, Except.pure] at success
        subst named
        obtain ⟨headEncoding, headValid⟩ := reifyTerm_correct state first called
        obtain ⟨tailEncoding, tailValid⟩ := reifyTerms_correct state rest children
        exact ⟨.cons headEncoding tailEncoding, by simpa using And.intro headValid tailValid⟩
termination_by sizeOf values
end

theorem reifyFormula_correct (state : State) (value : QuantifiedFOF.Formula) {named}
    (success : reifyFormula state value = .ok named) :
    TableFormulaEncoding state named value ∧ Tokens.FormulaNames named := by
  induction value generalizing named with
  | atom atom =>
    cases called : symbol state.predicates atom.pred atom.args.length with
    | error error => simp [reifyFormula, called, bind, Except.bind] at success
    | ok name =>
      cases children : reifyTerms state atom.args with
      | error error => simp [reifyFormula, called, children, bind, Except.bind] at success
      | ok args =>
        simp [reifyFormula, called, children, bind, Except.bind, pure, Except.pure] at success
        subst named
        obtain ⟨valid, found, arity⟩ := symbol_correct called
        obtain ⟨encoded, validTerms⟩ := reifyTerms_correct state atom.args children
        rw [← encoded.length] at arity
        exact ⟨.atom name atom.pred args atom.args found arity encoded, by simpa [Tokens.FormulaNames, Tokens.TermNames] using And.intro valid validTerms⟩
  | truth =>
    simp [reifyFormula, pure, Except.pure] at success
    subst named
    exact ⟨.truth, trivial⟩
  | falsity =>
    simp [reifyFormula, pure, Except.pure] at success
    subst named
    exact ⟨.falsity, trivial⟩
  | neg body ih =>
    cases called : reifyFormula state body with
    | error error => simp [reifyFormula, called, bind, Except.bind] at success
    | ok output =>
      simp [reifyFormula, called, bind, Except.bind, pure, Except.pure] at success
      subst named
      obtain ⟨encoded, valid⟩ := ih called
      exact ⟨.neg encoded, valid⟩
  | conj left right ihl ihr | disj left right ihl ihr | implies left right ihl ihr =>
    cases first : reifyFormula state left with
    | error error => simp [reifyFormula, first, bind, Except.bind] at success
    | ok l =>
      cases second : reifyFormula state right with
      | error error => simp [reifyFormula, first, second, bind, Except.bind] at success
      | ok r =>
        simp [reifyFormula, first, second, bind, Except.bind, pure, Except.pure] at success
        subst named
        obtain ⟨leftEncoding, leftValid⟩ := ihl first
        obtain ⟨rightEncoding, rightValid⟩ := ihr second
        exact ⟨by constructor <;> assumption, leftValid, rightValid⟩
  | all id body ih | ex id body ih =>
    cases bound : variableAt state id with
    | error error => simp [reifyFormula, bound, bind, Except.bind] at success
    | ok name =>
      cases child : reifyFormula state body with
      | error error => simp [reifyFormula, bound, child, bind, Except.bind] at success
      | ok output =>
        simp [reifyFormula, bound, child, bind, Except.bind, pure, Except.pure] at success
        subst named
        obtain ⟨validName, found⟩ := variableAt_correct bound
        obtain ⟨encoded, valid⟩ := ih child
        exact ⟨by constructor <;> assumption, validName, valid⟩

theorem reifyFormula_closed {state value named}
    (success : reifyFormula state value = .ok named) (closed : value.Within []) :
    named.Within [] :=
  (reifyFormula_correct state value success).1.closed_iff.mp closed

/-- This only emits a formula body. Row framing and the proof DAG are separate. -/
def render (state : State) (value : QuantifiedFOF.Formula) : Except String String := do
  Bytes.render (← reifyFormula state value)

theorem render_correct {state value text} (success : render state value = .ok text) :
    ∃ named, TableFormulaEncoding state named value ∧ Tokens.FormulaNames named ∧
      Bytes.ParsesFormula (spelling text) named := by
  cases called : reifyFormula state value with
  | error error => simp [render, called, bind, Except.bind] at success
  | ok named =>
    have printed : Bytes.render named = .ok text := by
      simpa [render, called, bind, Except.bind] using success
    obtain ⟨encoded, valid⟩ := reifyFormula_correct state value called
    exact ⟨named, encoded, valid, Bytes.render_formula valid printed⟩

theorem render_closed {state value text} (success : render state value = .ok text)
    (closed : value.Within []) :
    ∃ named, Bytes.ParsesFormula (spelling text) named ∧ named.Within [] ∧
      TableFormulaEncoding state named value := by
  obtain ⟨named, encoded, _, parsed⟩ := render_correct success
  exact ⟨named, parsed, encoded.closed_iff.mp closed, encoded⟩

theorem render_holds {state value text} (success : render state value = .ok text)
    {D : Type} (model : Source.Interpretation D) (valuation : Nat → D) :
    ∃ named, Bytes.ParsesFormula (spelling text) named ∧
      (value.Holds (model.toNumeric (symbolsFrom state)) valuation ↔
        named.Holds model (fun name => valuation ((variablesFrom state.variables).id name))) := by
  obtain ⟨named, encoded, _, parsed⟩ := render_correct success
  exact ⟨named, parsed, encoded.holds_toNumeric model valuation⟩

def renderClosed (state : State) (value : QuantifiedFOF.Formula) : Except String String :=
  if formulaWithin [] value then render state value
  else .error "export-error: formula has free variables"

theorem renderClosed_correct {state value text}
    (success : renderClosed state value = .ok text) :
    ∃ named, Bytes.ParsesFormula (spelling text) named ∧ named.Within [] ∧
      TableFormulaEncoding state named value := by
  by_cases closed : formulaWithin [] value = true
  · have printed : render state value = .ok text := by simpa [renderClosed, closed] using success
    exact render_closed printed ((formulaWithin_correct [] value).mp closed)
  · simp [renderClosed, closed] at success

#print axioms Fang.QuantifiedTstp.Naming.variableAt_correct
#print axioms Fang.QuantifiedTstp.Naming.symbol_correct
#print axioms Fang.QuantifiedTstp.Naming.reifyTerm_correct
#print axioms Fang.QuantifiedTstp.Naming.reifyTerms_correct
#print axioms Fang.QuantifiedTstp.Naming.reifyFormula_correct
#print axioms Fang.QuantifiedTstp.Naming.reifyFormula_closed
#print axioms Fang.QuantifiedTstp.Naming.render_correct
#print axioms Fang.QuantifiedTstp.Naming.render_closed
#print axioms Fang.QuantifiedTstp.Naming.render_holds
#print axioms Fang.QuantifiedTstp.Naming.renderClosed_correct

end Fang.QuantifiedTstp.Naming
