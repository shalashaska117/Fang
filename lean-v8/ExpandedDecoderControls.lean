/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed controls of the linear declaration decoder: exact names, offsets and
   body ends on a CNF and a FOF declaration, and the accepted errors for a
   repeated name, an unsupported role and a missing closing parenthesis. -/
import ExpandedDecoder

namespace Fang.TptpCandidate.FullFof.Integration.DecoderControls
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration

def bytesOf (text : String) : List UInt8 := text.toUTF8.data.toList

def mixed : String := "cnf(a,axiom,( p(X) | ~ q(f(X)) )).\nfof(b,axiom,![X]:(p(X)=>?[Y]:(q(Y)&X=Y)))."

def offsets (values : List Declaration) : List (Name × Nat × Nat × Nat × Nat) :=
  values.map fun value => (value.name, value.start, value.stop, value.bodyStart, value.bodyStop)

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

theorem cnf_and_fof_offsets :
    (decodeBytesLinear (bytesOf mixed) 1048576).map offsets =
      .ok [(.atom "a", 0, 34, 12, 32), (.atom "b", 35, 77, 47, 75)] := by cbv

theorem false_clause_offsets :
    (decodeBytesLinear (bytesOf "cnf(c,axiom,$false).") 1048576).map offsets = .ok [(.atom "c", 0, 20, 12, 18)] := by
  cbv

theorem repeated_name_rejected :
    (decodeBytesLinear (bytesOf "fof(a,axiom,p).\nfof(a,axiom,q).") 1048576).map offsets = .error ⟨.invalid, 20⟩ := by
  cbv

theorem conjecture_role_rejected :
    (decodeBytesLinear (bytesOf "fof(a,conjecture,p).") 1048576).map offsets = .error ⟨.unsupported, 6⟩ := by cbv

theorem missing_parenthesis_rejected :
    (decodeBytesLinear (bytesOf "cnf(a,axiom,p(X)|q(X).") 1048576).map offsets = .error ⟨.invalid, 21⟩ := by cbv

#print axioms Fang.TptpCandidate.FullFof.Integration.DecoderControls.cnf_and_fof_offsets
#print axioms Fang.TptpCandidate.FullFof.Integration.DecoderControls.false_clause_offsets
#print axioms Fang.TptpCandidate.FullFof.Integration.DecoderControls.repeated_name_rejected
#print axioms Fang.TptpCandidate.FullFof.Integration.DecoderControls.conjecture_role_rejected
#print axioms Fang.TptpCandidate.FullFof.Integration.DecoderControls.missing_parenthesis_rejected

end Fang.TptpCandidate.FullFof.Integration.DecoderControls
