/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent constant normalization retains every source declaration. -/
import CnfBoolean
import CnfBooleanByteSemantics

namespace Fang.TptpCandidate.FullFof.BooleanCnf

def classify : Formula → Literal Formula
  | .truth => .boolean true true
  | .falsity => .boolean true false
  | .neg .truth => .boolean false true
  | .neg .falsity => .boolean false false
  | value => .ordinary value

def literalHolds (eval : α → Prop) : Literal α → Prop
  | .ordinary value => eval value
  | .boolean positive value => positive = value

theorem classify_holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) (value : Formula) :
    literalHolds (Formula.Holds model valuation) (classify value) ↔ value.Holds model valuation := by
  cases value with
  | neg body => cases body <;> simp [classify, literalHolds, Formula.Holds]
  | atom _ _ | equal _ _ | truth | falsity | pair _ _ _ | all _ _ | ex _ _ =>
    simp [classify, literalHolds, Formula.Holds]

theorem raw_cons (eval : α → Prop) (value : Literal α) (rest : List (Literal α)) :
    rawHolds eval (value :: rest) ↔ literalHolds eval value ∨ rawHolds eval rest := by
  cases value <;> rfl

theorem classified_holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) (values : List Formula) :
    rawHolds (Formula.Holds model valuation) (values.map classify) ↔
      (Body.cnf values).formula.Holds model valuation := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simpa only [List.map_cons, Body.formula, List.foldr_cons, Formula.Holds, Binary.meaning]
      using (raw_cons _ (classify value) (rest.map classify)).trans
        (or_congr (classify_holds model valuation value) ih)

theorem clause_holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) (values : List Formula) :
    clauseHolds (Formula.Holds model valuation) values ↔
      (Body.cnf values).formula.Holds model valuation := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    exact or_congr Iff.rfl ih

def normalizedBody : Body → List Formula
  | .fof value => [value]
  | .cnf values =>
    match normalize (values.map classify) with
    | none => []
    | some literals => [(Body.cnf literals).formula]

theorem normalizedBody_holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) (body : Body) :
    (∀ value ∈ normalizedBody body, value.Holds model valuation) ↔ body.formula.Holds model valuation := by
  cases body with
  | fof value => simp [normalizedBody, Body.formula]
  | cnf values =>
    have normalized := (normalize_holds (Formula.Holds model valuation) (values.map classify)).trans
      (classified_holds model valuation values)
    cases outcome : normalize (values.map classify) with
    | none => simpa [normalizedBody, outcome, outputHolds] using normalized
    | some literals =>
      simpa [normalizedBody, outcome, outputHolds, clause_holds] using normalized

structure PreparedDeclaration where
  original : Declaration
  formulas : List Formula

def prepare (values : List Declaration) : List PreparedDeclaration :=
  values.map (fun value => ⟨value, normalizedBody value.body⟩)

theorem prepare_originals (values : List Declaration) :
    (prepare values).map PreparedDeclaration.original = values := by
  simp [prepare, Function.comp_def]

theorem prepare_length (values : List Declaration) : (prepare values).length = values.length := by
  simp [prepare]

def normalizedSource (values : List Declaration) : List Formula :=
  (prepare values).flatMap PreparedDeclaration.formulas

theorem normalized_models {D : Type} (model : Source.Interpretation D)
    (values : List Declaration) : Models (normalizedSource values) model ↔ Models (source values) model := by
  constructor
  · intro normalized value member valuation
    obtain ⟨declaration, present, rfl⟩ := List.mem_map.mp member
    apply (normalizedBody_holds model valuation declaration.body).mp
    intro formula included
    apply normalized formula _ valuation
    simp only [normalizedSource, prepare, List.flatMap_map, List.mem_flatMap]
    exact ⟨declaration, present, included⟩
  · intro original formula member valuation
    simp only [normalizedSource, prepare, List.flatMap_map, List.mem_flatMap] at member
    obtain ⟨declaration, present, included⟩ := member
    apply (normalizedBody_holds model valuation declaration.body).mpr _ formula included
    exact original declaration.body.formula (List.mem_map.mpr ⟨declaration, present, rfl⟩) valuation

theorem decode_normalized_models {input maximum values}
    (success : CnfBoolean.decodeBytes input maximum = .ok values) {D : Type}
    (model : Source.Interpretation D) :
    CnfBoolean.BytesModels input maximum model ↔ Models (normalizedSource values) model :=
  (CnfBoolean.decode_byte_models success model).trans (normalized_models model values).symm

end Fang.TptpCandidate.FullFof.BooleanCnf
