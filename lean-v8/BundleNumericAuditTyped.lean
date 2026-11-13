/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Audit rows, `$distinct`, `$ite`, `$let` and the type names: the outcome kind of the bundle framer
   and of the accepted single-file decoder on each sample, by evaluation. -/
import BundleNumericAuditBase

namespace Fang.TptpCandidate.FullFof.Coverage.NumericAudit

set_option maxRecDepth 20000 in
theorem audit_typed :
  framerKind "fof(a,axiom,$distinct(a,b))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$distinct(a,b))." = some .unsupported ∧
  framerKind "cnf(a,axiom,$distinct(a,b))." = some .unsupported ∧
  decoderKind "cnf(a,axiom,$distinct(a,b))." = some .unsupported ∧
  framerKind "fof(a,axiom,$ite(p,q,r))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$ite(p,q,r))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($ite(q,a,b)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($ite(q,a,b)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($let(a)))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($let(a)))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($i))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($i))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($o))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($o))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($int))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($int))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($rat))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($rat))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($real))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($real))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($tType))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($tType))." = some .unsupported := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.NumericAudit.audit_typed

end Fang.TptpCandidate.FullFof.Coverage.NumericAudit
