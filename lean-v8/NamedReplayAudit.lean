/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed audit of the replay with naming: the two endpoints and the signature
   result are stated here again with their full types, and the axioms of the
   main results are printed here rather than by the module that proves them. -/
import NamedReplay

open Aeneas.Std Fang.TptpCandidate.FullFof.Integration Fang.TptpCandidate.FullFof.Integration.Named

example {limit : Nat} {bytes : List UInt8} {maximumBytes : Nat} {limits : FangOriginalReplay.Limits}
    {threshold maximumPredicates maximumLiterals : Usize} {prepared : ReplayPrepared}
    (success : prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
      .ok prepared)
    (certificate : Fang.Equality.Ordered.Certificate)
    (accepted : Fang.Equality.Ordered.check prepared.problem certificate = .ok ()) :
    ¬ Fang.TptpCandidate.FullFof.CnfBoolean.BytesSatisfiable bytes maximumBytes :=
  prepareNamed_check_original_unsat success certificate accepted

example {limit : Nat} {bytes : List UInt8} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {threshold maximumPredicates maximumLiterals : Usize}
    (accepted : acceptsNamed limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals =
      .ok ()) :
    ¬ Fang.TptpCandidate.FullFof.CnfBoolean.BytesSatisfiable bytes maximumBytes :=
  acceptsNamed_original_unsat accepted

example {limit : Nat} {bytes : List UInt8} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {threshold maximumPredicates maximumLiterals : Usize}
    (accepted : acceptsNamed limit bytes maximumBytes proof limits threshold maximumPredicates maximumLiterals =
      .ok ()) :
    ∃ prepared, prepareNamed limit bytes maximumBytes limits threshold maximumPredicates maximumLiterals =
        .ok prepared ∧
      prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed prepared.functionArities
        prepared.predicateArities) = true :=
  acceptsNamed_signature accepted

#print axioms Fang.TptpCandidate.FullFof.Integration.Named.nnfBelow_sound
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.problem_agreeBelow
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.replayNamedBlocks_models
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.previous_renumber
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.renumber_models
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.prepareNamed_check_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.acceptsNamed_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.acceptsNamed_signature
