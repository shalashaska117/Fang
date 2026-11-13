/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   A refutation and a model are never both accepted for the same input: for each path, the native refutation entry
   and the model entry conclude contradictory statements about the same original bytes. -/
import ModelEntries

namespace Fang.TptpCandidate.FullFof.Model

open Aeneas.Std

theorem single_exclusive {limit limit' : Nat} {bytes : List UInt8} {maximumBytes : Nat} {proof : String}
    {replayLimits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize} {limits : Limits}
    {certificate : String}
    (refuted : Integration.acceptsLimited limit bytes maximumBytes proof replayLimits maximumPredicates
      maximumLiterals = .ok ())
    (model : acceptsSingle limits limit' bytes maximumBytes certificate = .ok ()) : False :=
  Integration.acceptsLimited_original_unsat refuted (acceptsSingle_satisfiable model)

theorem bundle_exclusive {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat} {proof : String}
    {replayLimits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize} {limits : Limits}
    {certificate : String}
    (refuted : Coverage.BundleLimit.acceptsBundle Coverage.BundleLimit.limited files maximumBytes proof replayLimits
      maximumPredicates maximumLiterals = .ok ())
    (model : acceptsBundle limits Coverage.BundleLimit.limited files maximumBytes certificate = .ok ()) : False :=
  (Coverage.BundleLimit.acceptsBundleLimited_refuted refuted).2 (acceptsBundleLimited_satisfiable model)

theorem inputs_exclusive {files : List (Coverage.Key × List UInt8)} {maximumBytes : Nat} {proof : String}
    {replayLimits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize} {limits : Limits}
    {certificate : String}
    (refuted : Roles.Bundle.V3.acceptsInputs Roles.Bundle.V3.limited files maximumBytes proof replayLimits
      maximumPredicates maximumLiterals = .ok ())
    (model : acceptsInputs limits Roles.Bundle.V3.limited files maximumBytes certificate = .ok ()) : False :=
  Roles.Bundle.V3.inputsSatisfiable_not_unsatisfiable (acceptsInputsLimited_satisfiable model)
    (Roles.Bundle.V3.acceptsInputsLimited_unsat refuted)

/-- A proof and a countermodel of the same selected conjecture (the same bundle item), whatever indices the two runs
    were given. -/
theorem goal_exclusive {files : List (Coverage.Key × List UInt8)} {maximumBytes index index' : Nat} {proof : String}
    {replayLimits : FangOriginalReplay.Limits} {maximumPredicates maximumLiterals : Usize} {limits : Limits}
    {certificate : String} {item : Coverage.Item}
    (refuted : Roles.Bundle.V3.acceptsGoal Roles.Bundle.V3.limited files maximumBytes index proof replayLimits
      maximumPredicates maximumLiterals = .ok item)
    (model : acceptsGoal limits Roles.Bundle.V3.limited files maximumBytes index' certificate = .ok item) : False :=
  Roles.Bundle.V3.countermodel_not_entailed (acceptsGoalLimited_countermodel model)
    (Roles.Bundle.V3.acceptsGoalLimited_entails refuted)

/-- A countermodel of one selected conjecture excludes the SZS Theorem statement for the bundle. -/
theorem goal_not_theorem {files : List (Coverage.Key × List UInt8)} {maximumBytes index : Nat} {limits : Limits}
    {certificate : String} {item : Coverage.Item}
    (model : acceptsGoal limits Roles.Bundle.V3.limited files maximumBytes index certificate = .ok item) :
    ¬ Roles.Bundle.V3.ByteTheorem Roles.Bundle.V3.limitedSpecification files maximumBytes Roles.Bundle.bundleFuel :=
  Roles.Bundle.V3.counterSatisfiable_not_theorem (acceptsGoalLimited_counterSatisfiable model)

end Fang.TptpCandidate.FullFof.Model
