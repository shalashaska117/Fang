/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Original function reservation for later model extension. -/
import ExpandedSource
import SkolemModel

namespace Fang.TptpCandidate.FullFof.Integration
open BooleanCnf QuantifiedFOF.Skolem

theorem encoded_term_below (term : Source.Term) (functions : Arity.Table)
    (variables : Source.Variables) (covered : Arity.TermCovered functions term) :
    TermBelow functions.length (Arity.encodeTerm functions variables term) := by
  cases term with
  | var name => simp [Arity.encodeTerm, TermBelow]
  | app name args =>
    simp only [Arity.encodeTerm, TermBelow]
    refine ⟨Arity.id_bound (covered _ (by simp [Arity.termFunctions])), ?_⟩
    intro value member
    obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
    apply encoded_term_below child functions variables
    intro symbol included
    apply covered symbol
    simp only [Arity.termFunctions]
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, present, included⟩)
termination_by sizeOf term

theorem lowered_below {left right : QuantifiedFOF.Formula} {limit}
    (operator : Binary) (l : FormulaBelow limit left) (r : FormulaBelow limit right) :
    FormulaBelow limit (operator.lower left right) := by
  cases operator <;> simp_all [Binary.lower, FormulaBelow]

theorem encoded_formula_below (formula : Formula) (functions predicates : Arity.Table)
    (variables : Source.Variables) (covered : ∀ symbol ∈ formula.functions, symbol ∈ functions) :
    FormulaBelow functions.length (formula.encode functions predicates variables) := by
  induction formula with
  | atom name args =>
    intro value member
    obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
    exact encoded_term_below child functions variables
      (fun symbol included => covered symbol (List.mem_flatMap.mpr ⟨child, present, included⟩))
  | equal left right =>
    intro value member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact encoded_term_below left functions variables
        (fun symbol included => covered symbol (List.mem_append_left _ included))
    · exact encoded_term_below right functions variables
        (fun symbol included => covered symbol (List.mem_append_right _ included))
  | truth | falsity => trivial
  | neg body ih | all name body ih | ex name body ih => exact ih covered
  | pair operator left right ihl ihr =>
    exact lowered_below operator
      (ihl (fun symbol included => covered symbol (List.mem_append_left _ included)))
      (ihr (fun symbol included => covered symbol (List.mem_append_right _ included)))

def LiteralBelow (limit : Nat) (literal : Fang.Literal) : Prop :=
  ∀ term ∈ literal.atom.args, TermBelow limit term

theorem readLiteral_below {formula literal limit}
    (success : readLiteral formula = some literal) (below : FormulaBelow limit formula) :
    LiteralBelow limit literal := by
  cases formula with
  | atom atom => cases Option.some.inj success; exact below
  | neg body =>
    cases body with
    | atom atom => cases Option.some.inj success; exact below
    | truth | falsity | neg _ | conj _ _ | disj _ _ | implies _ _ | all _ _ | ex _ _ => cases success
  | truth | falsity | conj _ _ | disj _ _ | implies _ _ | all _ _ | ex _ _ => cases success

theorem readRaw_below {functions predicates variables source literal}
    (success : readRaw functions predicates variables source = some (.ordinary literal))
    (covered : ∀ symbol ∈ source.functions, symbol ∈ functions) :
    LiteralBelow functions.length literal := by
  cases classified : classify source with
  | boolean positive value => simp [readRaw, classified] at success
  | ordinary value =>
    have same := classify_ordinary classified
    subst value
    cases result : readLiteral (source.encode functions predicates variables) with
    | none => simp [readRaw, classified, result] at success
    | some actual =>
      have same : actual = literal := by simpa [readRaw, classified, result] using success
      subst literal
      exact readLiteral_below result (encoded_formula_below source functions predicates variables covered)

theorem readRaws_below {functions predicates variables sources targets}
    (success : readRaws functions predicates variables sources = some targets)
    (covered : ∀ source ∈ sources, ∀ symbol ∈ source.functions, symbol ∈ functions) :
    ∀ literal ∈ ordinary targets, LiteralBelow functions.length literal := by
  induction sources generalizing targets with
  | nil => cases Option.some.inj success; simp [ordinary]
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
        have restBelow := ih tailRun (fun value member => covered value (by simp [member]))
        cases first with
        | boolean positive value => exact restBelow
        | ordinary literal =>
          intro value member
          rcases List.mem_cons.mp member with rfl | member
          · exact readRaw_below firstRun (covered source (by simp))
          · exact restBelow value member

theorem readClause_below {functions predicates variables sources target}
    (success : readClause functions predicates variables sources = some (some target))
    (covered : ∀ source ∈ sources, ∀ symbol ∈ source.functions, symbol ∈ functions) :
    ∀ literal ∈ target, LiteralBelow functions.length literal := by
  cases raw : readRaws functions predicates variables sources with
  | none => simp [readClause, raw] at success
  | some literals =>
    have normalized : normalize literals = some target :=
      Option.some.inj (by simpa [readClause, raw] using success)
    rw [normalize_some normalized]
    exact readRaws_below raw covered

def DeclarationBelow (limit : Nat) : NumericDeclaration → Prop
  | .cnf clause => ∀ literal ∈ clause, LiteralBelow limit literal
  | .fof formula => FormulaBelow limit formula

theorem readBody_below {functions predicates body targets}
    (success : readBody functions predicates body = some targets)
    (covered : body.formula.Covered functions predicates body.formula.variables) :
    ∀ target ∈ targets, DeclarationBelow functions.length target := by
  cases body with
  | fof formula =>
    cases Option.some.inj success
    intro target member
    have same : target = .fof (formula.encode functions predicates formula.variables) := by simpa using member
    subst target
    exact encoded_formula_below formula functions predicates formula.variables covered.functions
  | cnf literals =>
    cases result : readClause functions predicates (Body.cnf literals).formula.variables literals with
    | none => simp [readBody, result] at success
    | some output =>
      have same : cnfBlock output = targets := Option.some.inj (by simpa [readBody, result] using success)
      subst targets
      cases output with
      | none => simp [cnfBlock]
      | some clause =>
        intro target member
        have same : target = .cnf clause := by simpa [cnfBlock] using member
        subst target
        exact readClause_below result (fun value member => (cnf_member_covered covered member).functions)

theorem readRows_below {functions predicates values rows}
    (success : readRows functions predicates values = some rows)
    (covered : ∀ value ∈ values, value.body.formula.Covered functions predicates value.body.formula.variables) :
    ∀ target ∈ rows.flatMap NumericRow.declarations, DeclarationBelow functions.length target := by
  induction values generalizing rows with
  | nil => cases Option.some.inj success; simp
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
        intro target member
        rcases List.mem_append.mp member with member | member
        · exact readBody_below bodyAt (covered first (by simp)) target member
        · exact ih tailAt (fun value present => covered value (by simp [present])) target member

theorem readInput_below {values input} (success : readInput values = some input) :
    ∀ target ∈ input.declarations, DeclarationBelow input.functions.length target := by
  cases rowsAt : readRows (functionTable (source values)) (predicateTable (source values)) values with
  | none => simp [readInput, rowsAt] at success
  | some rows =>
    have same : (⟨functionTable (source values), predicateTable (source values), rows⟩ : NumericInput) = input :=
      Option.some.inj (by simpa [readInput, rowsAt] using success)
    subst input
    exact readRows_below rowsAt (fun value member =>
      collected_covered (List.mem_map.mpr ⟨value, member, rfl⟩))

#print axioms Fang.TptpCandidate.FullFof.Integration.encoded_term_below
#print axioms Fang.TptpCandidate.FullFof.Integration.lowered_below
#print axioms Fang.TptpCandidate.FullFof.Integration.encoded_formula_below
#print axioms Fang.TptpCandidate.FullFof.Integration.readLiteral_below
#print axioms Fang.TptpCandidate.FullFof.Integration.readRaw_below
#print axioms Fang.TptpCandidate.FullFof.Integration.readRaws_below
#print axioms Fang.TptpCandidate.FullFof.Integration.readClause_below
#print axioms Fang.TptpCandidate.FullFof.Integration.readBody_below
#print axioms Fang.TptpCandidate.FullFof.Integration.readRows_below
#print axioms Fang.TptpCandidate.FullFof.Integration.readInput_below

end Fang.TptpCandidate.FullFof.Integration
