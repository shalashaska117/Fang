/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Checked export tables with fresh functions and fresh naming predicates. -/
import ExpandedDocument
import ExpandedSap

namespace Fang.QuantifiedEqualityTstp.NamedExport
open Fang.TptpCandidate.FullFof.Integration

structure Checked (originalFunctions originalPredicates : List (String × Nat))
    (prepared : FangQuantifiedEqualityReplay.Prepared) (names : Body.Names) : Prop where
  functionPrefix : QuantifiedTstp.Tables.isPrefix (Naming.symbols originalFunctions) names.functions = true
  predicatePrefix : QuantifiedTstp.Tables.isPrefix (Naming.symbols originalPredicates) names.predicates = true
  freshNames : Naming.fresh (Naming.originalNames originalFunctions originalPredicates)
    (names.functions.drop originalFunctions.length ++ names.predicates.drop originalPredicates.length) = true
  functionArities : names.functions.map Frontend.Symbol.arity = prepared.functionArities.map some
  predicateArities : names.predicates.map Frontend.Symbol.arity = prepared.predicateArities.map some
  functionKeys : (Naming.keys names.functions).Nodup
  predicateKeys : (Naming.keys names.predicates).Nodup

def check (originalFunctions originalPredicates : List (String × Nat))
    (prepared : FangQuantifiedEqualityReplay.Prepared) (names : Body.Names) : Except String Body.Names :=
  if QuantifiedTstp.Tables.isPrefix (Naming.symbols originalFunctions) names.functions &&
      QuantifiedTstp.Tables.isPrefix (Naming.symbols originalPredicates) names.predicates &&
      Naming.fresh (Naming.originalNames originalFunctions originalPredicates)
        (names.functions.drop originalFunctions.length ++ names.predicates.drop originalPredicates.length) &&
      decide (names.functions.map Frontend.Symbol.arity = prepared.functionArities.map some) &&
      decide (names.predicates.map Frontend.Symbol.arity = prepared.predicateArities.map some) &&
      decide (Naming.keys names.functions).Nodup && decide (Naming.keys names.predicates).Nodup then
    .ok names
  else .error "export-error: symbol tables, arities or fresh names differ"

theorem check_spec {originalFunctions originalPredicates prepared names checked}
    (success : check originalFunctions originalPredicates prepared names = .ok checked) :
    Checked originalFunctions originalPredicates prepared checked := by
  unfold check at success
  split at success
  next checks =>
    cases Except.ok.inj success
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checks
    exact ⟨checks.1.1.1.1.1.1, checks.1.1.1.1.1.2, checks.1.1.1.1.2,
      checks.1.1.1.2, checks.1.1.2, checks.1.2, checks.2⟩
  next => cases success

def exportNames (originalFunctions originalPredicates : List (String × Nat))
    (functions predicates : List Nat) : Body.Names :=
  let original := Naming.originalNames originalFunctions originalPredicates
  let functionStem := Expanded.freshPrefix original "sk" "f"
  let functionNames := Naming.symbols originalFunctions ++
    (functions.drop originalFunctions.length).mapIdx fun index arity =>
      ⟨functionStem ++ toString index, some arity⟩
  let predicateStem := Expanded.freshPrefix (original ++ functionNames.map Frontend.Symbol.name) "nm" "p"
  let predicateNames := Naming.symbols originalPredicates ++
    (predicates.drop originalPredicates.length).mapIdx fun index arity =>
      ⟨predicateStem ++ toString index, some arity⟩
  ⟨functionNames, predicateNames⟩

theorem namedModel_models {originalFunctions originalPredicates : List (String × Nat)}
    {prepared : FangQuantifiedEqualityReplay.Prepared} {names : Body.Names}
    (checked : Checked originalFunctions originalPredicates prepared names)
    (wellFormed : prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed
      prepared.functionArities prepared.predicateArities) = true)
    {D : Type} (model : Fang.Interpretation D) (holds : Fang.Equality.models model prepared.problem) :
    Fang.Equality.models (TstpText.tableModel names.view (Expanded.namedModel names model)) prepared.problem := by
  intro clause member
  apply (Expanded.clause_agree prepared.functionArities prepared.predicateArities ?_ ?_
    (List.all_eq_true.mp wellFormed clause member)).mp (holds clause member)
  · intro index arguments arity
    obtain ⟨entry, found, entryArity⟩ := Expanded.table_entry checked.functionArities arity
    have nameAt : Frontend.tableName names.functions index = entry.name := by
      simp [Frontend.tableName, found]
    simp only [TstpText.tableModel, Expanded.namedModel, Body.Names.view]
    rw [nameAt, Expanded.keyIndex_exact checked.functionKeys found entryArity]
  · intro index arguments arity
    obtain ⟨entry, found, entryArity⟩ := Expanded.table_entry checked.predicateArities arity
    have nameAt : Frontend.tableName names.predicates index = entry.name := by
      simp [Frontend.tableName, found]
    simp only [TstpText.tableModel, Expanded.namedModel, Body.Names.view]
    rw [nameAt, Expanded.keyIndex_exact checked.predicateKeys found entryArity]

end Fang.QuantifiedEqualityTstp.NamedExport
