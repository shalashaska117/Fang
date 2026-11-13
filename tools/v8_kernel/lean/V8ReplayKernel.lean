/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compose actual version-8 calls on one input without repeating their reductions.
   Each premise is a separately checked equation about the same bytes. -/
import ExpandedCertificate

open Aeneas Aeneas.Std
namespace FangV8KernelGenerator
open Fang.TptpCandidate.FullFof.Integration

/-- The version-8 transport is the reviewed version-7 transport applied to the
    legacy representation, so a version-7 transport equation transfers. -/
theorem transport_of_legacy {numeric decoded maximum encoded}
    (legacy : legacyInput numeric = decoded)
    (transportRun : FangQuantifiedEqualityInput.transport decoded maximum = .ok encoded) :
    transport numeric maximum = .ok encoded := by
  rw [transport, legacy, transportRun]

/-- The mixed assembly in `prepare` reads the numeric rows; the legacy rows carry
    the same declarations. -/
theorem assembly_of_legacy {numeric decoded blocks ordinary}
    (legacy : legacyInput numeric = decoded)
    (assemblyRun : FangOriginalReplay.assemble
      (FangQuantifiedEqualityInput.numericDeclarations decoded.declarations) blocks = .ok ordinary) :
    FangOriginalReplay.assemble numeric.declarations blocks = .ok ordinary := by
  subst legacy
  simpa only [legacyInput, legacy_rows_numeric, NumericInput.declarations] using assemblyRun

theorem prepare_of_parts {bytes maximumBytes limits maximumPredicates maximumLiterals
    numeric encoded transformed blocks ordinary equality}
    (decodeRun : decodeNumeric bytes maximumBytes = .ok numeric)
    (transportRun : transport numeric maximumPredicates = .ok encoded)
    (skolemRun : fang_skolem_core.skolemize_problem encoded.declarations encoded.signature
      limits.skolem = .ok (.Ok transformed))
    (blocksRun : FangOriginalReplay.replayBlocks limits transformed.formulas.val = .ok blocks)
    (assemblyRun : FangOriginalReplay.assemble numeric.declarations blocks = .ok ordinary)
    (conversionRun : FangQuantifiedEqualityReplay.Conversion.problem
      encoded.reservation maximumLiterals ordinary = .ok equality) :
    prepare bytes maximumBytes limits maximumPredicates maximumLiterals = .ok {
      original := numeric
      problem := equality
      functionArities := transformed.signature.functions.val.map (fun value => value.val)
      predicateArities := numeric.predicates.map Prod.snd } := by
  simp only [prepare, decodeRun, transportRun, skolemRun, Except.mapError, Bind.bind, Except.bind,
    FangOriginalReplay.observe, Result.match.ok, blocksRun, assemblyRun, conversionRun, Pure.pure, Except.pure]

theorem accepts_of_parts {bytes maximumBytes proof limits maximumPredicates maximumLiterals prepared}
    (prepareRun : prepare bytes maximumBytes limits maximumPredicates maximumLiterals = .ok prepared)
    (checkRun : checkProblem prepared.problem prepared.functionArities prepared.predicateArities proof = .ok ()) :
    accepts bytes maximumBytes proof limits maximumPredicates maximumLiterals = .ok () := by
  simp only [accepts, prepareRun, checkRun, Except.mapError, Bind.bind, Except.bind]

#print axioms FangV8KernelGenerator.transport_of_legacy
#print axioms FangV8KernelGenerator.assembly_of_legacy
#print axioms FangV8KernelGenerator.prepare_of_parts
#print axioms FangV8KernelGenerator.accepts_of_parts
end FangV8KernelGenerator
