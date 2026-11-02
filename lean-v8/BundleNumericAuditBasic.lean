/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Audit rows, supported forms: truth values, equality, integer formula names, numbers inside annotations, distinct objects and pragma comments: the outcome kind of the bundle framer
   and of the accepted single-file decoder on each sample, by evaluation. -/
import BundleNumericAuditBase

namespace Fang.TptpCandidate.FullFof.Coverage.NumericAudit

set_option maxRecDepth 20000 in
theorem audit_basic :
  framerKind "fof(a,axiom,$true & ~$false)." = none ∧
  decoderKind "fof(a,axiom,$true & ~$false)." = none ∧
  framerKind "cnf(a,axiom,a = b | c != d)." = none ∧
  decoderKind "cnf(a,axiom,a = b | c != d)." = none ∧
  framerKind "fof(12,axiom,p)." = none ∧
  decoderKind "fof(12,axiom,p)." = none ∧
  framerKind "fof(a,axiom,p,[1,-2,3/4,5.5,6e7])." = none ∧
  decoderKind "fof(a,axiom,p,[1,-2,3/4,5.5,6e7])." = some .unsupported ∧
  framerKind "fof(a,axiom,p(\"u\") & ~p(\"v\"))." = none ∧
  decoderKind "fof(a,axiom,p(\"u\") & ~p(\"v\"))." = some .unsupported ∧
  framerKind "%$ pragma\n/*$$Otter */ fof(a,axiom,p)." = none ∧
  decoderKind "%$ pragma\n/*$$Otter */ fof(a,axiom,p)." = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.NumericAudit.audit_basic

end Fang.TptpCandidate.FullFof.Coverage.NumericAudit
