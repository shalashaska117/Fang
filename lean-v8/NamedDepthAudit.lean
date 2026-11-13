/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed audit of the expanded entry with naming at a height parameter: the
   endpoint and the signature result are stated here again with their full
   types, and the axioms of the four results are printed here. -/
import NamedDepthEntry

open Aeneas.Std Fang.TptpCandidate.FullFof.Integration Fang.TptpCandidate.FullFof.Integration.Named

example {limit maxDepth : Nat} {bytes : List UInt8} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {threshold maximumPredicates maximumLiterals : Usize}
    (accepted : acceptsNamedD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ¬ Fang.TptpCandidate.FullFof.CnfBoolean.BytesSatisfiable bytes maximumBytes :=
  acceptsNamedD_original_unsat accepted

example {limit maxDepth : Nat} {bytes : List UInt8} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {threshold maximumPredicates maximumLiterals : Usize}
    (accepted : acceptsNamedD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates
      maximumLiterals = .ok ()) :
    ∃ prepared, prepareNamedD limit maxDepth bytes maximumBytes limits threshold maximumPredicates
        maximumLiterals = .ok prepared ∧
      prepared.problem.all (Fang.EqualityCertificateInput.clauseWellFormed prepared.functionArities
        prepared.predicateArities) = true :=
  acceptsNamedD_signature accepted

example (limit : Nat) : acceptsNamedD limit 64 = acceptsNamed limit := acceptsNamedD_accepted limit

#print axioms Fang.TptpCandidate.FullFof.Integration.Named.prepareNamedD_check_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.acceptsNamedD_original_unsat
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.acceptsNamedD_signature
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.acceptsNamedD_accepted
