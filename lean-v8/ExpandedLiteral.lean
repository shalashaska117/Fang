/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Checked literal transport over the independent expanded frontend model. -/
import CnfBooleanNormalize

namespace Fang.TptpCandidate.FullFof.Integration
open BooleanCnf

/-- Only an atom or its direct negation is a numeric CNF literal. -/
def readLiteral : QuantifiedFOF.Formula → Option Fang.Literal
  | .atom atom => some ⟨true, atom⟩
  | .neg (.atom atom) => some ⟨false, atom⟩
  | _ => none

theorem readLiteral_holds {formula literal} (success : readLiteral formula = some literal)
    {D : Type} (model : Interpretation D) (valuation : Nat → D) :
    literal.Holds model valuation ↔ formula.Holds model valuation := by
  cases formula with
  | atom atom =>
    cases Option.some.inj success
    rfl
  | neg body =>
    cases body with
    | atom atom =>
      cases Option.some.inj success
      rfl
    | truth | falsity | neg _ | conj _ _ | disj _ _ | implies _ _ | all _ _ | ex _ _ =>
      cases success
  | truth | falsity | conj _ _ | disj _ _ | implies _ _ | all _ _ | ex _ _ =>
    cases success

theorem classify_ordinary {source target}
    (same : classify source = .ordinary target) : target = source := by
  cases source with
  | neg body => cases body <;> simp_all [classify]
  | atom _ _ | equal _ _ | truth | falsity | pair _ _ _ | all _ _ | ex _ _ =>
    simp_all [classify]

/-- Visit all raw literals before normalization; a true constant does not skip
    a later malformed ordinary literal. Original tables and variables are inputs. -/
def readRaw (functions predicates : Arity.Table) (variables : Source.Variables)
    (source : Formula) : Option (BooleanCnf.Literal Fang.Literal) :=
  match classify source with
  | .boolean positive value => some (.boolean positive value)
  | .ordinary value =>
    (readLiteral (value.encode functions predicates variables)).map .ordinary

theorem readRaw_holds {functions predicates variables source target}
    (success : readRaw functions predicates variables source = some target)
    (covered : source.Covered functions predicates variables)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement functions predicates named numeric)
    (namedValuation : String → D) (numericValuation : Nat → D)
    (values : NamedQuantified.ValuationsAgree variables namedValuation numericValuation) :
    literalHolds (Fang.Literal.Holds numeric numericValuation) target ↔
      source.Holds named namedValuation := by
  cases classified : classify source with
  | boolean positive value =>
    have same : .boolean positive value = target :=
      Option.some.inj (by simpa only [readRaw, classified] using success)
    subst target
    simpa only [classified, literalHolds] using classify_holds named namedValuation source
  | ordinary value =>
    have same := classify_ordinary classified
    subst value
    cases read : readLiteral (source.encode functions predicates variables) with
    | none => simp [readRaw, classified, read] at success
    | some literal =>
      have targetEq : .ordinary literal = target :=
        Option.some.inj (by simpa only [readRaw, classified, read, Option.map_some] using success)
      subst target
      exact (readLiteral_holds read numeric numericValuation).trans
        (encode_holds covered models namedValuation numericValuation values)

def readRaws (functions predicates : Arity.Table) (variables : Source.Variables) :
    List Formula → Option (List (BooleanCnf.Literal Fang.Literal))
  | [] => some []
  | source :: rest => do
    let first ← readRaw functions predicates variables source
    let tail ← readRaws functions predicates variables rest
    pure (first :: tail)

theorem readRaws_holds {functions predicates variables sources targets}
    (success : readRaws functions predicates variables sources = some targets)
    (covered : ∀ source ∈ sources, source.Covered functions predicates variables)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement functions predicates named numeric)
    (namedValuation : String → D) (numericValuation : Nat → D)
    (values : NamedQuantified.ValuationsAgree variables namedValuation numericValuation) :
    rawHolds (Fang.Literal.Holds numeric numericValuation) targets ↔
      (Body.cnf sources).formula.Holds named namedValuation := by
  induction sources generalizing targets with
  | nil =>
    cases Option.some.inj success
    rfl
  | cons source rest ih =>
    cases firstRun : readRaw functions predicates variables source with
    | none => simp [readRaws, firstRun] at success
    | some first =>
      cases tailRun : readRaws functions predicates variables rest with
      | none => simp [readRaws, firstRun, tailRun] at success
      | some tail =>
        have same : first :: tail = targets :=
          Option.some.inj (by simpa [readRaws, firstRun, tailRun] using success)
        subst targets
        rw [raw_cons]
        exact or_congr
          (readRaw_holds firstRun (covered source (by simp)) models _ _ values)
          (ih tailRun (fun value member => covered value (by simp [member])))

def readClause (functions predicates : Arity.Table) (variables : Source.Variables)
    (sources : List Formula) : Option (Option Fang.Clause) :=
  (readRaws functions predicates variables sources).map normalize

theorem readClause_holds {functions predicates variables sources target}
    (success : readClause functions predicates variables sources = some target)
    (covered : ∀ source ∈ sources, source.Covered functions predicates variables)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement functions predicates named numeric)
    (namedValuation : String → D) (numericValuation : Nat → D)
    (values : NamedQuantified.ValuationsAgree variables namedValuation numericValuation) :
    outputHolds (Fang.Literal.Holds numeric numericValuation) target ↔
      (Body.cnf sources).formula.Holds named namedValuation := by
  cases raw : readRaws functions predicates variables sources with
  | none => simp [readClause, raw] at success
  | some literals =>
    have same : normalize literals = target :=
      Option.some.inj (by simpa only [readClause, raw, Option.map_some] using success)
    subst target
    exact (normalize_holds _ _).trans
      (readRaws_holds raw covered models namedValuation numericValuation values)

theorem zero_and_empty :
    readClause [] [] Formula.truth.variables [.truth] = some none ∧
    readClause [] [] Formula.falsity.variables [.falsity] = some (some []) := by decide

theorem truth_does_not_skip_nonliteral :
    readClause [] [] Formula.truth.variables
      [.truth, .pair .conj .truth .truth] = none := by decide

#print axioms Fang.TptpCandidate.FullFof.Integration.readLiteral_holds
#print axioms Fang.TptpCandidate.FullFof.Integration.classify_ordinary
#print axioms Fang.TptpCandidate.FullFof.Integration.readRaw_holds
#print axioms Fang.TptpCandidate.FullFof.Integration.readRaws_holds
#print axioms Fang.TptpCandidate.FullFof.Integration.readClause_holds
#print axioms Fang.TptpCandidate.FullFof.Integration.zero_and_empty
#print axioms Fang.TptpCandidate.FullFof.Integration.truth_does_not_skip_nonliteral

end Fang.TptpCandidate.FullFof.Integration
