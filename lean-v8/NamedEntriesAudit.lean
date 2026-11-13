/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Endpoint types and axiom reports for naming in signed and bundle entries. -/
import NamedBundle
import NamedRoleBundle

open Aeneas.Std

namespace Fang.TptpCandidate.Roles.Signed
example {limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsInputsNamed limit bytes maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximumBytes :=
  acceptsInputsNamed_unsat accepted

example {limit bytes maximumBytes index proof limits threshold maximumPredicates maximumLiterals}
    (accepted : acceptsGoalNamed limit bytes maximumBytes index proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ∃ prepared, prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧
      ∃ values, Bytes.ByteParsed bytes maximumBytes values ∧ Bytes.Closed values ∧
        prepared.goal ∈ Roles.goals (Bytes.source values) ∧
        ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
          Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
            Bytes.sentence model prepared.goal.original :=
  acceptsGoalNamed_entails accepted

example {limit bytes maximumBytes values limits threshold maximumPredicates maximumLiterals}
    (decoded : Bytes.decodeBytesLimited limit bytes maximumBytes = .ok values)
    (nonempty : Roles.goals (Bytes.source values) ≠ [])
    (accepted : ∀ goal ∈ Roles.goals (Bytes.source values), ∃ index prepared proof,
      prepareGoalNamed limit bytes maximumBytes index limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧ prepared.goal = goal ∧
      acceptsGoalNamed limit bytes maximumBytes index proof limits threshold maximumPredicates maximumLiterals =
        .ok ()) :
    BytesTheorem bytes maximumBytes :=
  acceptsGoalsNamed_theorem decoded nonempty accepted
end Fang.TptpCandidate.Roles.Signed

namespace Fang.TptpCandidate.FullFof.Coverage.BundleLimit
example {files maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : Named.acceptsBundle limited files maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    BundleRefuted limitedSpecification files maximumBytes BundleV8.bundleFuel :=
  Named.acceptsBundleLimited_refuted accepted
end Fang.TptpCandidate.FullFof.Coverage.BundleLimit

namespace Fang.TptpCandidate.Roles.Bundle.V3
example {files maximumBytes index proof limits threshold maximumPredicates maximumLiterals item}
    (accepted : Named.acceptsGoal limited files maximumBytes index proof limits threshold maximumPredicates
      maximumLiterals = .ok item) :
    GoalEntailed limitedSpecification files maximumBytes bundleFuel item :=
  Named.acceptsGoalLimited_entails accepted

example {files maximumBytes proof limits threshold maximumPredicates maximumLiterals}
    (accepted : Named.acceptsInputs limited files maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ByteUnsatisfiable limitedSpecification files maximumBytes bundleFuel :=
  Named.acceptsInputsLimited_unsat accepted

example {files maximumBytes bundle items limits threshold maximumPredicates maximumLiterals}
    (expanded : Expanded limitedSpecification files maximumBytes bundleFuel bundle items)
    (nonempty : goalItems bundle items ≠ [])
    (accepted : ∀ pair ∈ goalItems bundle items, ∃ index proof,
      Named.acceptsGoal limited files maximumBytes index proof limits threshold maximumPredicates maximumLiterals =
        .ok pair.1) :
    ByteTheorem limitedSpecification files maximumBytes bundleFuel :=
  Named.acceptsGoalsLimited_theorem expanded nonempty accepted
end Fang.TptpCandidate.Roles.Bundle.V3

#print axioms Fang.TptpCandidate.FullFof.Integration.Named.named_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.replayNamedFrom_check_unsat
#print axioms Fang.TptpCandidate.Roles.Signed.replayNamedTask_check_unsat_below
#print axioms Fang.TptpCandidate.Roles.Signed.replayNamedTask_check_unsat
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoalNamed_entails
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsInputsNamed_unsat
#print axioms Fang.TptpCandidate.Roles.Signed.acceptsGoalsNamed_theorem
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Named.acceptsBundle_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Named.acceptsBundle_refuted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Named.acceptsBundleHashed_refuted
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleLimit.Named.acceptsBundleLimited_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.prepareGoal_check_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.prepareInputs_check_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsGoal_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsInputs_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsGoals_theorem
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsGoalLimited_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsInputsLimited_unsat
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.Named.acceptsGoalsLimited_theorem
