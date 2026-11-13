/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Audit rows, the arithmetic predicates and functions: the outcome kind of the bundle framer
   and of the accepted single-file decoder on each sample, by evaluation. -/
import BundleNumericAuditBase

namespace Fang.TptpCandidate.FullFof.Coverage.NumericAudit

set_option maxRecDepth 20000 in
theorem audit_arithmetic :
  framerKind "fof(a,axiom,$less(a,b))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$less(a,b))." = some .unsupported ∧
  framerKind "fof(a,axiom,$lesseq(a,b))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$lesseq(a,b))." = some .unsupported ∧
  framerKind "fof(a,axiom,$greater(a,b))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$greater(a,b))." = some .unsupported ∧
  framerKind "fof(a,axiom,$greatereq(a,b))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$greatereq(a,b))." = some .unsupported ∧
  framerKind "fof(a,axiom,$is_int(a))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$is_int(a))." = some .unsupported ∧
  framerKind "fof(a,axiom,$is_rat(a))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$is_rat(a))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($uminus(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($uminus(a)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($sum(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($sum(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($difference(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($difference(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($product(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($product(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($quotient(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($quotient(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($quotient_e(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($quotient_e(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($quotient_t(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($quotient_t(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($quotient_f(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($quotient_f(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($remainder_e(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($remainder_e(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($remainder_t(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($remainder_t(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($remainder_f(a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($remainder_f(a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($floor(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($floor(a)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($ceiling(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($ceiling(a)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($truncate(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($truncate(a)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($round(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($round(a)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($abs(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($abs(a)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($to_int(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($to_int(a)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($to_rat(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($to_rat(a)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($to_real(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($to_real(a)))." = some .unsupported := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.NumericAudit.audit_arithmetic

end Fang.TptpCandidate.FullFof.Coverage.NumericAudit
