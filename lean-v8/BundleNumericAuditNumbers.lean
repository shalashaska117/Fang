/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Audit rows, integer, rational and real terms: the outcome kind of the bundle framer
   and of the accepted single-file decoder on each sample, by evaluation. -/
import BundleNumericAuditBase

namespace Fang.TptpCandidate.FullFof.Coverage.NumericAudit

set_option maxRecDepth 20000 in
theorem audit_numbers :
  framerKind "fof(a,axiom,p(1))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p(1))." = some .unsupported ∧
  framerKind "fof(a,axiom,p(-7))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p(-7))." = some .unsupported ∧
  framerKind "fof(a,axiom,p(1/2))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p(1/2))." = some .unsupported ∧
  framerKind "fof(a,axiom,p(1.5))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p(1.5))." = some .unsupported ∧
  framerKind "fof(a,axiom,p(1.5e-3))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p(1.5e-3))." = some .unsupported ∧
  framerKind "fof(a,axiom,1 = 2)." = some .unsupported ∧
  decoderKind "fof(a,axiom,1 = 2)." = some .unsupported ∧
  framerKind "cnf(a,axiom,X != 0)." = some .unsupported ∧
  decoderKind "cnf(a,axiom,X != 0)." = some .unsupported := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.NumericAudit.audit_numbers

end Fang.TptpCandidate.FullFof.Coverage.NumericAudit
