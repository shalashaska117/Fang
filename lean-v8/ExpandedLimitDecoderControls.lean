/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed controls of the decoder with a declaration limit parameter: the limit
   stops the third declaration at limit 2 and lets it through at limit 3, and a
   repeated name gives the accepted error. The hashed decoder is checked through
   its equality with the list decoder, since string hashing does not reduce in
   the kernel. -/
import ExpandedLimitDecoder

namespace Fang.TptpCandidate.FullFof.Integration.LimitControls
open Fang.TptpCandidate.FullFof Fang.TptpCandidate.FullFof.Integration

def bytesOf (text : String) : List UInt8 := text.toUTF8.data.toList

def three : String := "cnf(a,axiom,p).\ncnf(b,axiom,q).\nfof(c,axiom,r)."

def names (values : List Declaration) : List Fang.TptpCandidate.Name := values.map Declaration.name

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

theorem limit_reached : (decodeBytesUpTo 2 (bytesOf three) 1048576).map names = .error ⟨.resource, 32⟩ := by cbv

theorem limit_not_reached :
    (decodeBytesUpTo 3 (bytesOf three) 1048576).map names = .ok [.atom "a", .atom "b", .atom "c"] := by cbv

theorem repeated_name_rejected :
    (decodeBytesUpTo 3 (bytesOf "fof(a,axiom,p).\nfof(a,axiom,q).") 1048576).map names = .error ⟨.invalid, 20⟩ := by
  cbv

theorem hashed_limit_reached :
    (decodeBytesLimited 2 (bytesOf three) 1048576).map names = .error ⟨.resource, 32⟩ := by
  rw [decodeBytesLimited_eq]
  exact limit_reached

theorem hashed_limit_not_reached :
    (decodeBytesLimited 3 (bytesOf three) 1048576).map names = .ok [.atom "a", .atom "b", .atom "c"] := by
  rw [decodeBytesLimited_eq]
  exact limit_not_reached

#print axioms Fang.TptpCandidate.FullFof.Integration.LimitControls.limit_reached
#print axioms Fang.TptpCandidate.FullFof.Integration.LimitControls.limit_not_reached
#print axioms Fang.TptpCandidate.FullFof.Integration.LimitControls.repeated_name_rejected
#print axioms Fang.TptpCandidate.FullFof.Integration.LimitControls.hashed_limit_reached
#print axioms Fang.TptpCandidate.FullFof.Integration.LimitControls.hashed_limit_not_reached

end Fang.TptpCandidate.FullFof.Integration.LimitControls
