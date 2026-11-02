/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Complete original tables and source records precede Boolean omission. -/
import ExpandedScope
import QuantifiedProblem

namespace Fang.TptpCandidate.FullFof.Integration
open BooleanCnf

abbrev NumericDeclaration := NamedQuantified.NumericDeclaration

def cnfBlock : Option Fang.Clause → List NumericDeclaration
  | none => []
  | some clause => [.cnf clause]

def BodyClosed : Body → Prop
  | .cnf _ => True
  | .fof value => value.Within []

def readBody (functions predicates : Arity.Table) (body : Body) :
    Option (List NumericDeclaration) :=
  match body with
  | .fof formula => some [.fof (formula.encode functions predicates formula.variables)]
  | .cnf literals => do
    let result ← readClause functions predicates body.formula.variables literals
    pure (cnfBlock result)

structure NumericRow where
  original : Declaration
  declarations : List NumericDeclaration

def readRows (functions predicates : Arity.Table) :
    List Declaration → Option (List NumericRow)
  | [] => some []
  | value :: rest => do
    let body ← readBody functions predicates value.body
    let tail ← readRows functions predicates rest
    pure (⟨value, body⟩ :: tail)

structure NumericInput where
  functions : Arity.Table
  predicates : Arity.Table
  rows : List NumericRow

def readInput (values : List Declaration) : Option NumericInput := do
  let functions := functionTable (source values)
  let predicates := predicateTable (source values)
  let rows ← readRows functions predicates values
  pure ⟨functions, predicates, rows⟩

def NumericInput.declarations (input : NumericInput) : List NumericDeclaration :=
  input.rows.flatMap NumericRow.declarations

theorem cnf_functions (values : List Formula) :
    (Body.cnf values).formula.functions = values.flatMap Formula.functions := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simpa only [Body.formula, List.foldr_cons, Formula.functions, List.flatMap_cons] using
      congrArg (value.functions ++ ·) ih

theorem cnf_predicates (values : List Formula) :
    (Body.cnf values).formula.predicates = values.flatMap Formula.predicates := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simpa only [Body.formula, List.foldr_cons, Formula.predicates, List.flatMap_cons] using
      congrArg (value.predicates ++ ·) ih

theorem cnf_variables (values : List Formula) :
    (Body.cnf values).formula.variableNames = values.flatMap Formula.variableNames := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simpa only [Body.formula, List.foldr_cons, Formula.variableNames, List.flatMap_cons] using
      congrArg (value.variableNames ++ ·) ih

theorem cnf_member_covered {functions predicates variables values}
    (covered : (Body.cnf values).formula.Covered functions predicates variables)
    {value} (member : value ∈ values) : value.Covered functions predicates variables := by
  constructor
  · intro symbol present
    apply covered.functions
    rw [cnf_functions]
    exact List.mem_flatMap.mpr ⟨value, member, present⟩
  · intro symbol present
    apply covered.predicates
    rw [cnf_predicates]
    exact List.mem_flatMap.mpr ⟨value, member, present⟩
  · intro name present
    apply covered.variables
    rw [cnf_variables]
    exact List.mem_flatMap.mpr ⟨value, member, present⟩

theorem numeric_clause_holds {D : Type} (model : Interpretation D)
    (valuation : Nat → D) (clause : Fang.Clause) :
    clauseHolds (Fang.Literal.Holds model valuation) clause ↔ clause.Holds model valuation := by
  induction clause with
  | nil => simp [clauseHolds, Fang.Clause.Holds]
  | cons first rest ih => simpa [clauseHolds, Fang.Clause.Holds] using or_congr Iff.rfl ih

theorem readBody_models {functions predicates body targets}
    (success : readBody functions predicates body = some targets)
    (covered : body.formula.Covered functions predicates body.formula.variables)
    (closed : BodyClosed body)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement functions predicates named numeric) :
    NamedQuantified.NumericModels numeric targets ↔ ∀ valuation, body.formula.Holds named valuation := by
  cases body with
  | fof formula =>
    cases Option.some.inj success
    have within := encoded_formula_within formula functions predicates formula.variables [] closed
    constructor
    · intro holds valuation
      apply (encode_holds covered models valuation
        (fun id => valuation (formula.variables.name id))
        (fun _ represented => by simpa only [Body.formula] using congrArg valuation represented.symm)).mp
      exact (holds (.fof (formula.encode functions predicates formula.variables)) (by simp)).2 _
    · intro holds target member
      have same : target = .fof (formula.encode functions predicates formula.variables) := by simpa using member
      subst target
      refine ⟨within, ?_⟩
      intro valuation
      exact (encode_holds covered models (fun name => valuation (formula.variables.id name))
        valuation (fun _ _ => rfl)).mpr (holds _)
  | cnf literals =>
    cases result : readClause functions predicates (Body.cnf literals).formula.variables literals with
    | none => simp [readBody, result] at success
    | some output =>
      have same : cnfBlock output = targets :=
        Option.some.inj (by simpa [readBody, result] using success)
      subst targets
      have meaning := readClause_holds result (fun value member => cnf_member_covered covered member) models
      cases output with
      | none =>
        constructor
        · intro _ valuation
          exact (meaning valuation (fun id => valuation ((Body.cnf literals).formula.variables.name id))
            (fun _ represented => by simp [represented])).mp trivial
        · intro _ target member; simp [cnfBlock] at member
      | some clause =>
        constructor
        · intro holds valuation
          apply (meaning valuation (fun id => valuation ((Body.cnf literals).formula.variables.name id))
            (fun _ represented => by simp [represented])).mp
          exact (numeric_clause_holds numeric _ clause).mpr (holds (.cnf clause) (by simp [cnfBlock]) _)
        · intro holds target member
          have same : target = .cnf clause := by simpa [cnfBlock] using member
          subst target
          intro valuation
          apply (numeric_clause_holds numeric valuation clause).mp
          exact (meaning (fun name => valuation ((Body.cnf literals).formula.variables.id name))
            valuation (fun _ _ => rfl)).mpr (holds _)

theorem readRows_originals {functions predicates values rows}
    (success : readRows functions predicates values = some rows) :
    rows.map NumericRow.original = values := by
  induction values generalizing rows with
  | nil => cases Option.some.inj success; rfl
  | cons first rest ih =>
    cases bodyAt : readBody functions predicates first.body with
    | none => simp [readRows, bodyAt] at success
    | some body =>
      cases tailAt : readRows functions predicates rest with
      | none => simp [readRows, bodyAt, tailAt] at success
      | some tail =>
        have same : (⟨first, body⟩ :: tail : List NumericRow) = rows :=
          Option.some.inj (by simpa [readRows, bodyAt, tailAt] using success)
        subst rows
        simpa using congrArg (first :: ·) (ih tailAt)

theorem readRows_models {functions predicates values rows}
    (success : readRows functions predicates values = some rows)
    (covered : ∀ value ∈ values, value.body.formula.Covered functions predicates value.body.formula.variables)
    (closed : Grammar.Closed values)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement functions predicates named numeric) :
    NamedQuantified.NumericModels numeric (rows.flatMap NumericRow.declarations) ↔
      Models (source values) named := by
  induction values generalizing rows with
  | nil =>
    cases Option.some.inj success
    simp [NamedQuantified.NumericModels, Models, source]
  | cons first rest ih =>
    cases bodyAt : readBody functions predicates first.body with
    | none => simp [readRows, bodyAt] at success
    | some body =>
      cases tailAt : readRows functions predicates rest with
      | none => simp [readRows, bodyAt, tailAt] at success
      | some tail =>
        have same : (⟨first, body⟩ :: tail : List NumericRow) = rows :=
          Option.some.inj (by simpa [readRows, bodyAt, tailAt] using success)
        subst rows
        have head := readBody_models bodyAt (covered first (by simp))
          (by
            cases shape : first.body with
            | cnf _ => trivial
            | fof value => simpa [BodyClosed, shape] using closed first (by simp)) models
        have restModels := ih tailAt (fun value member => covered value (by simp [member]))
          (fun value member => closed value (by simp [member]))
        simpa only [List.flatMap_cons, NamedQuantified.NumericModels,
          List.forall_mem_append, source, List.map_cons, Models, List.forall_mem_cons,
          Function.comp_apply] using
          and_congr head restModels

theorem readInput_tables {values input} (success : readInput values = some input) :
    input.functions = functionTable (source values) ∧
    input.predicates = predicateTable (source values) ∧
    input.rows.map NumericRow.original = values := by
  cases rowsAt : readRows (functionTable (source values)) (predicateTable (source values)) values with
  | none => simp [readInput, rowsAt] at success
  | some rows =>
    have same : (⟨functionTable (source values), predicateTable (source values), rows⟩ : NumericInput) = input :=
      Option.some.inj (by simpa [readInput, rowsAt] using success)
    subst input
    exact ⟨rfl, rfl, readRows_originals rowsAt⟩

theorem readInput_models {values input} (success : readInput values = some input)
    (closed : Grammar.Closed values) {D : Type}
    {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement input.functions input.predicates named numeric) :
    NamedQuantified.NumericModels numeric input.declarations ↔ Models (source values) named := by
  cases rowsAt : readRows (functionTable (source values)) (predicateTable (source values)) values with
  | none => simp [readInput, rowsAt] at success
  | some rows =>
    have same : (⟨functionTable (source values), predicateTable (source values), rows⟩ : NumericInput) = input :=
      Option.some.inj (by simpa [readInput, rowsAt] using success)
    subst input
    exact readRows_models rowsAt (fun value member =>
      collected_covered (List.mem_map.mpr ⟨value, member, rfl⟩)) closed models

theorem decode_readInput_models {bytes maximum values input}
    (decoded : CnfBoolean.decodeBytes bytes maximum = .ok values)
    (encoded : readInput values = some input) {D : Type}
    {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement input.functions input.predicates named numeric) :
    CnfBoolean.BytesModels bytes maximum named ↔ NamedQuantified.NumericModels numeric input.declarations :=
  (CnfBoolean.decode_byte_models decoded named).trans
    (readInput_models encoded (CnfBoolean.decode_closed decoded) models).symm

/-- The final reserved predicate is interpreted as domain equality. -/
def NumericInput.Satisfiable (input : NumericInput) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Interpretation D),
    NamedQuantified.NumericModels (reserve input.predicates.length model) input.declarations

theorem readInput_satisfiable {values input} (success : readInput values = some input)
    (closed : Grammar.Closed values) :
    Satisfiable (source values) ↔ input.Satisfiable := by
  constructor
  · rintro ⟨domain, inhabited, model, holds⟩
    exact ⟨domain, inhabited, Arity.toNumeric model input.functions input.predicates,
      (readInput_models success closed (model_toNumeric model _ _)).mpr holds⟩
  · rintro ⟨domain, inhabited, model, holds⟩
    exact ⟨domain, inhabited, Arity.toNamed model input.functions input.predicates,
      (readInput_models success closed (model_toNamed model _ _)).mp holds⟩

theorem decode_readInput_satisfiable {bytes maximum values input}
    (decoded : CnfBoolean.decodeBytes bytes maximum = .ok values)
    (encoded : readInput values = some input) :
    CnfBoolean.BytesSatisfiable bytes maximum ↔ input.Satisfiable :=
  (CnfBoolean.decode_bytes_satisfiable decoded).trans
    (readInput_satisfiable encoded (CnfBoolean.decode_closed decoded))

theorem decode_readInput_unsat {bytes maximum values input}
    (decoded : CnfBoolean.decodeBytes bytes maximum = .ok values)
    (encoded : readInput values = some input) (refuted : ¬ input.Satisfiable) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximum :=
  fun model => refuted ((decode_readInput_satisfiable decoded encoded).mp model)

#print axioms Fang.TptpCandidate.FullFof.Integration.cnf_functions
#print axioms Fang.TptpCandidate.FullFof.Integration.cnf_predicates
#print axioms Fang.TptpCandidate.FullFof.Integration.cnf_variables
#print axioms Fang.TptpCandidate.FullFof.Integration.cnf_member_covered
#print axioms Fang.TptpCandidate.FullFof.Integration.numeric_clause_holds
#print axioms Fang.TptpCandidate.FullFof.Integration.readBody_models
#print axioms Fang.TptpCandidate.FullFof.Integration.readRows_originals
#print axioms Fang.TptpCandidate.FullFof.Integration.readRows_models
#print axioms Fang.TptpCandidate.FullFof.Integration.readInput_tables
#print axioms Fang.TptpCandidate.FullFof.Integration.readInput_models
#print axioms Fang.TptpCandidate.FullFof.Integration.decode_readInput_models
#print axioms Fang.TptpCandidate.FullFof.Integration.readInput_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Integration.decode_readInput_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Integration.decode_readInput_unsat

end Fang.TptpCandidate.FullFof.Integration
