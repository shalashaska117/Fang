/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The satisfiability-preserving direction of version-8 preparation, carried to
   the named group formula: a model of the original bytes yields a source model
   of the printed group under the checked export names. -/
import ExpandedCertificate
import EqualityGroup

namespace Fang.QuantifiedEqualityTstp.Expanded
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration
open Fang.QuantifiedCertificate FangQuantifiedPipeline

/-- Every model of the original bytes gives a model of the actual prepared problem. -/
theorem prepare_models {bytes maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepare bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (satisfiable : CnfBoolean.BytesSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
      Fang.Equality.models model prepared.problem := by
  obtain ⟨values, encoded, transformed, blocks, ordinary, decoded, numericRun,
    inputRun, skolemRun, steps, layout, converted, _, _⟩ := prepare_witness success
  obtain ⟨D, nonempty, original, holds⟩ := (decode_readInput_satisfiable decoded numericRun).mp satisfiable
  let : Nonempty D := nonempty
  obtain ⟨valid, _, slot, _, _, _⟩ := transport_tables inputRun
  have originalHolds := transport_models inputRun holds
  have reservedHolds :
      (retained prepared.original.declarations).Models
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original) ∧
      SignedDeclarationsHold
        (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
        encoded.declarations.val := by
    rw [slot, ← reserve_interpretation]
    exact originalHolds
  obtain ⟨extended, preserved, grouped⟩ := skolem_actual_problem_models skolemRun
    (retained prepared.original.declarations) (transport_retained_below numericRun inputRun)
    blocks steps (Fang.EqualityBridge.reserveInterpretation encoded.reservation.equality.val original)
  have groupedModel := grouped.mpr reservedHolds
  have mixedModel : ordinary.Models extended := (mixedLayout_models layout extended).mpr
    ((FangQuantifiedPipeline.models_append extended _ _).mp groupedModel)
  have equalityModel := (FangQuantifiedEquality.actualProblem_models original extended
    encoded.reservation encoded.signature.functions.val.length valid preserved converted).mp mixedModel
  exact ⟨D, nonempty, Fang.EqualityBridge.recoverInterpretation original extended, equalityModel⟩

/-! ### Agreement on well-formed terms -/

section Agreement
variable {D : Type} {M N : Fang.Interpretation D}

mutual
theorem term_agree (arities : List Nat)
    (agree : ∀ index (arguments : List D), arities[index]? = some arguments.length →
      M.function index arguments = N.function index arguments) (valuation : Nat → D) :
    ∀ (term : Fang.Term), Fang.termWellFormed arities term = true →
      term.eval M valuation = term.eval N valuation
  | .var _, _ => by simp only [Fang.Term.eval]
  | .app symbol arguments, wellFormed => by
    simp only [Fang.termWellFormed, Bool.and_eq_true, beq_iff_eq] at wellFormed
    simp only [Fang.Term.eval]
    rw [terms_agree arities agree valuation arguments wellFormed.2]
    exact agree symbol _ (by simpa using wellFormed.1)

theorem terms_agree (arities : List Nat)
    (agree : ∀ index (arguments : List D), arities[index]? = some arguments.length →
      M.function index arguments = N.function index arguments) (valuation : Nat → D) :
    ∀ (terms : List Fang.Term), Fang.termsWellFormed arities terms = true →
      terms.map (Fang.Term.eval M valuation) = terms.map (Fang.Term.eval N valuation)
  | [], _ => rfl
  | first :: rest, wellFormed => by
    simp only [Fang.termsWellFormed, Bool.and_eq_true] at wellFormed
    simp only [List.map_cons, term_agree arities agree valuation first wellFormed.1,
      terms_agree arities agree valuation rest wellFormed.2]
end

theorem clause_agree (functions predicates : List Nat)
    (functionAgree : ∀ index (arguments : List D), functions[index]? = some arguments.length →
      M.function index arguments = N.function index arguments)
    (predicateAgree : ∀ index (arguments : List D), predicates[index]? = some arguments.length →
      (M.predicate index arguments ↔ N.predicate index arguments))
    {clause : Fang.Equality.Clause}
    (wellFormed : Fang.EqualityCertificateInput.clauseWellFormed functions predicates clause = true) :
    Fang.Equality.clauseValid M clause ↔ Fang.Equality.clauseValid N clause := by
  have literal : ∀ literal ∈ clause, ∀ valuation,
      (literal.Holds M valuation ↔ literal.Holds N valuation) := by
    intro literal member valuation
    have checked := List.all_eq_true.mp wellFormed literal member
    obtain ⟨positive, atom⟩ := literal
    cases atom with
    | predicate atom =>
      simp only [Bool.and_eq_true, beq_iff_eq] at checked
      have same : (Fang.Equality.Atom.predicate atom).Holds M valuation ↔
          (Fang.Equality.Atom.predicate atom).Holds N valuation := by
        simp only [Fang.Equality.Atom.Holds, Fang.Atom.Holds]
        rw [terms_agree functions functionAgree valuation atom.args checked.2]
        exact predicateAgree atom.pred _ (by simpa using checked.1)
      cases positive <;> simp [Fang.Equality.Literal.Holds, same]
    | equal left right =>
      simp only [Bool.and_eq_true] at checked
      have same : (Fang.Equality.Atom.equal left right).Holds M valuation ↔
          (Fang.Equality.Atom.equal left right).Holds N valuation := by
        simp only [Fang.Equality.Atom.Holds,
          term_agree functions functionAgree valuation left checked.1,
          term_agree functions functionAgree valuation right checked.2]
      cases positive <;> simp [Fang.Equality.Literal.Holds, same]
  constructor
  · intro valid valuation
    obtain ⟨value, member, holds⟩ := valid valuation
    exact ⟨value, member, (literal value member valuation).mp holds⟩
  · intro valid valuation
    obtain ⟨value, member, holds⟩ := valid valuation
    exact ⟨value, member, (literal value member valuation).mpr holds⟩

end Agreement

/-! ### A named model reading each name and arity at its table entry -/

def keyIndex : List Frontend.Symbol → String → Nat → Nat
  | [], _, _ => 0
  | entry :: rest, symbol, arity =>
    if entry.name = symbol ∧ entry.arity = some arity then 0 else keyIndex rest symbol arity + 1

theorem keyIndex_exact {symbols : List Frontend.Symbol} (unique : (Naming.keys symbols).Nodup)
    {index : Nat} {entry : Frontend.Symbol} {arity : Nat}
    (found : symbols[index]? = some entry) (sameArity : entry.arity = some arity) :
    keyIndex symbols entry.name arity = index := by
  induction symbols generalizing index with
  | nil => simp at found
  | cons head rest ih =>
    simp only [Naming.keys, List.map_cons, List.nodup_cons] at unique
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp [keyIndex, sameArity]
    | succ index =>
      simp only [List.getElem?_cons_succ] at found
      have later := ih unique.2 found
      have different : ¬ (head.name = entry.name ∧ head.arity = some arity) := by
        rintro ⟨sameName, headArity⟩
        apply unique.1
        have member : (entry.name, entry.arity) ∈ Naming.keys rest :=
          List.mem_map.mpr ⟨entry, List.mem_of_getElem? found, rfl⟩
        simpa [Naming.keys, sameName, headArity, sameArity] using member
      simp [keyIndex, different, later]

def namedModel {D : Type} (names : Body.Names) (model : Fang.Interpretation D) :
    Source.Interpretation D where
  function symbol arguments := model.function (keyIndex names.functions symbol arguments.length) arguments
  predicate symbol arguments := model.predicate (keyIndex names.predicates symbol arguments.length) arguments

theorem table_entry {symbols : List Frontend.Symbol} {arities : List Nat}
    (same : symbols.map Frontend.Symbol.arity = arities.map some) {index arity : Nat}
    (found : arities[index]? = some arity) :
    ∃ entry, symbols[index]? = some entry ∧ entry.arity = some arity := by
  have atIndex := congrArg (·[index]?) same
  simp only [List.getElem?_map, found, Option.map_some] at atIndex
  cases entryAt : symbols[index]? with
  | none => simp [entryAt] at atIndex
  | some entry =>
    simp only [entryAt, Option.map_some, Option.some.injEq] at atIndex
    exact ⟨entry, rfl, atIndex⟩

theorem namedModel_models {originalFunctions originalPredicates : List (String × Nat)}
    {prepared : FangQuantifiedEqualityReplay.Prepared} {names : Body.Names}
    (checked : Naming.Checked originalFunctions originalPredicates prepared names)
    (wellFormed : prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed
      prepared.functionArities prepared.predicateArities) = true)
    {D : Type} (model : Fang.Interpretation D) (holds : Fang.Equality.models model prepared.problem) :
    Fang.Equality.models (TstpText.tableModel names.view (namedModel names model)) prepared.problem := by
  intro clause member
  apply (clause_agree prepared.functionArities prepared.predicateArities ?_ ?_
    (List.all_eq_true.mp wellFormed clause member)).mp (holds clause member)
  · intro index arguments arity
    obtain ⟨entry, found, entryArity⟩ := table_entry checked.functionArities arity
    have nameAt : Frontend.tableName names.functions index = entry.name := by
      simp [Frontend.tableName, found]
    simp only [TstpText.tableModel, namedModel, Body.Names.view]
    rw [nameAt, keyIndex_exact checked.functionKeys found entryArity]
  · intro index arguments arity
    obtain ⟨entry, found, entryArity⟩ := table_entry checked.predicateArities arity
    have nameAt : Frontend.tableName names.predicates index = entry.name := by
      simp [Frontend.tableName, found]
    simp only [TstpText.tableModel, namedModel, Body.Names.view]
    rw [nameAt, keyIndex_exact checked.predicateKeys found entryArity]

/-- SAP for the printed group: if the original bytes have a model, the closed
    group formula built from the actual prepared problem and checked names holds
    in some source model. -/
theorem group_sap {bytes maximumBytes limits maximumPredicates maximumLiterals prepared}
    (success : prepare bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    {originalFunctions originalPredicates : List (String × Nat)} {names : Body.Names}
    (checked : Naming.Checked originalFunctions originalPredicates
      ⟨prepared.problem, prepared.functionArities, prepared.predicateArities⟩ names)
    (wellFormed : prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed
      prepared.functionArities prepared.predicateArities) = true)
    {formula : NamedQuantifiedEquality.Formula}
    (formulaRun : Group.groupFormula names prepared.problem = .ok formula)
    (satisfiable : CnfBoolean.BytesSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨D, nonempty, model, holds⟩ := prepare_models success satisfiable
  have named := namedModel_models (prepared := ⟨prepared.problem, prepared.functionArities,
    prepared.predicateArities⟩) checked wellFormed model holds
  exact ⟨D, nonempty, namedModel names model,
    ((Group.groupFormula_spec formulaRun).2.2 (namedModel names model)).mpr named⟩

#print axioms Fang.QuantifiedEqualityTstp.Expanded.prepare_models
#print axioms Fang.QuantifiedEqualityTstp.Expanded.term_agree
#print axioms Fang.QuantifiedEqualityTstp.Expanded.terms_agree
#print axioms Fang.QuantifiedEqualityTstp.Expanded.clause_agree
#print axioms Fang.QuantifiedEqualityTstp.Expanded.keyIndex_exact
#print axioms Fang.QuantifiedEqualityTstp.Expanded.table_entry
#print axioms Fang.QuantifiedEqualityTstp.Expanded.namedModel_models
#print axioms Fang.QuantifiedEqualityTstp.Expanded.group_sap

end Fang.QuantifiedEqualityTstp.Expanded
