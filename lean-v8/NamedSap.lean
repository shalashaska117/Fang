/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   SAP for the group containing the named clauses and their definitions. -/
import NamedModels
import NamedNames

namespace Fang.QuantifiedEqualityTstp.NamedExport
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration

theorem group_models {originalFunctions originalPredicates : List (String × Nat)}
    {prepared : FangQuantifiedEqualityReplay.Prepared} {names : Body.Names}
    (checked : Checked originalFunctions originalPredicates prepared names)
    (wellFormed : prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed
      prepared.functionArities prepared.predicateArities) = true)
    {formula : NamedQuantifiedEquality.Formula}
    (formulaRun : Group.groupFormula names prepared.problem = .ok formula)
    {D : Type} (model : Fang.Interpretation D) (holds : Fang.Equality.models model prepared.problem) :
    ∀ valuation, formula.Holds (Expanded.namedModel names model) valuation :=
  ((Group.groupFormula_spec formulaRun).2.2 (Expanded.namedModel names model)).mpr
    (namedModel_models checked wellFormed model holds)

theorem group_sap {limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals prepared}
    (success : Named.prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    {originalFunctions originalPredicates : List (String × Nat)} {names : Body.Names}
    (checked : Checked originalFunctions originalPredicates
      ⟨prepared.problem, prepared.functionArities, prepared.predicateArities⟩ names)
    (wellFormed : prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed
      prepared.functionArities prepared.predicateArities) = true)
    {formula : NamedQuantifiedEquality.Formula}
    (formulaRun : Group.groupFormula names prepared.problem = .ok formula)
    (satisfiable : CnfBoolean.BytesSatisfiable bytes maximumBytes) :
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      ∀ valuation, formula.Holds model valuation := by
  obtain ⟨D, nonempty, model, holds⟩ := Named.prepareNamed_models success satisfiable
  exact ⟨D, nonempty, Expanded.namedModel names model,
    group_models checked wellFormed formulaRun model holds⟩

end Fang.QuantifiedEqualityTstp.NamedExport
