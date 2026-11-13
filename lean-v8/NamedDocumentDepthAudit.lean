/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed audit of the named single-file document at a height parameter: the
   export endpoint is stated here again with its full type, and the axioms of
   the main results are printed here. -/
import NamedDocumentDepth

open Aeneas.Std Fang.TptpCandidate.FullFof Fang.QuantifiedEqualityTstp.NamedExport

example {limit maxDepth : Nat} {bytes : List UInt8} {maximumBytes : Nat} {proof : String}
    {limits : FangOriginalReplay.Limits} {threshold maximumPredicates maximumLiterals : Usize} {file text : String}
    (success : exportDocumentD limit maxDepth bytes maximumBytes proof limits threshold maximumPredicates
      maximumLiterals file = .ok text) :
    ¬ CnfBoolean.BytesSatisfiable bytes maximumBytes :=
  exportDocumentD_original_unsat success

example (limit : Nat) : exportDocumentD limit 64 = exportDocument limit := exportDocumentD_accepted limit

#print axioms Fang.TptpCandidate.FullFof.Integration.Named.replayNamedFrom_original
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.prepareNamedD_models
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.prepareNamedD_original
#print axioms Fang.TptpCandidate.FullFof.Integration.Named.prepareNamedD_accepted
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.group_sapD
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.buildD_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.buildD_accepts
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.buildD_group_sap
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.originalsD_decoded
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.documentD_spec
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.documentD_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.documentD_group_sap
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.rowD_local
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.finalD_row_empty
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.exportDocumentD_spec
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.exportDocumentD_original_unsat
#print axioms Fang.QuantifiedEqualityTstp.NamedExport.exportDocumentD_accepted
