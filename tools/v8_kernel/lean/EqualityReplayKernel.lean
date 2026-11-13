/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Compose actual same-input calls without repeating their reductions. -/
import EqualityOriginalCertificate

open Aeneas Aeneas.Std
namespace FangEqualityKernelGenerator

theorem replay_blocks_cons {limits formula rest removed output blocks}
    (removeRun : fang_binder_removal_core.remove_universals
      (FangQuantifiedPipeline.skolemNnf formula) limits.removal = .ok (.Ok removed))
    (clauseRun : fang_fof_core.nnf_entry.clausify_nnf_from
      (FangQuantifiedPipeline.removedNnf removed.formula) limits.clausification
      FangOriginalReplay.initialStatistics = .ok (.Ok output))
    (tailRun : FangOriginalReplay.replayBlocks limits rest = .ok blocks) :
    FangOriginalReplay.replayBlocks limits (formula :: rest) =
      .ok (FangScopedFof.decodeClauses output.clauses.val :: blocks) := by
  rw [FangOriginalReplay.replayBlocks, removeRun]
  simp only [FangOriginalReplay.observe, Result.match.ok, Bind.bind, Except.bind]
  rw [clauseRun]
  simp only [Result.match.ok, tailRun, Pure.pure, Except.pure]

theorem prepare_of_parts {input limits maximumPredicates maximumLiterals
    encoded transformed blocks ordinary equality}
    (inputRun : FangQuantifiedEqualityInput.prepareInput input maximumPredicates = .ok encoded)
    (skolemRun : fang_skolem_core.skolemize_problem encoded.declarations encoded.signature
      limits.skolem = .ok (.Ok transformed))
    (blocksRun : FangOriginalReplay.replayBlocks limits transformed.formulas.val = .ok blocks)
    (assemblyRun : FangOriginalReplay.assemble
      (FangQuantifiedEqualityInput.numericDeclarations encoded.original.declarations) blocks = .ok ordinary)
    (conversionRun : FangQuantifiedEqualityReplay.Conversion.problem
      encoded.reservation maximumLiterals ordinary = .ok equality) :
    FangQuantifiedEqualityReplay.prepare input limits maximumPredicates maximumLiterals = .ok {
      problem := equality
      functionArities := transformed.signature.functions.val.map (fun value => value.val)
      predicateArities := encoded.original.originalPredicates.map Prod.snd } := by
  simp only [FangQuantifiedEqualityReplay.prepare, inputRun, skolemRun,
    Except.mapError, Bind.bind, Except.bind, FangOriginalReplay.observe, Result.match.ok,
    blocksRun, assemblyRun, conversionRun, Pure.pure, Except.pure]

theorem accepts_of_parts {input proof limits maximumPredicates maximumLiterals prepared}
    (prepareRun : FangQuantifiedEqualityReplay.prepare input limits maximumPredicates maximumLiterals = .ok prepared)
    (certificateRun : FangQuantifiedEqualityCertificate.checkPrepared
      prepared.problem prepared.functionArities prepared.predicateArities proof = .ok ()) :
    FangQuantifiedEqualityCertificate.accepts input proof limits maximumPredicates maximumLiterals = .ok () := by
  simp only [FangQuantifiedEqualityCertificate.accepts, prepareRun, certificateRun,
    Except.mapError, Bind.bind, Except.bind]

#print axioms FangEqualityKernelGenerator.replay_blocks_cons
#print axioms FangEqualityKernelGenerator.prepare_of_parts
#print axioms FangEqualityKernelGenerator.accepts_of_parts
end FangEqualityKernelGenerator
