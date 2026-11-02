/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Audit rows, undefined and system words, back-quoted words, formula data outside annotations, typed statements and sequents: the outcome kind of the bundle framer
   and of the accepted single-file decoder on each sample, by evaluation. -/
import BundleNumericAuditBase

namespace Fang.TptpCandidate.FullFof.Coverage.NumericAudit

set_option maxRecDepth 20000 in
theorem audit_other :
  framerKind "fof(a,axiom,$foo(a))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$foo(a))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($))." = some .unsupported ∧
  framerKind "fof(a,axiom,$$foo(a))." = some .unsupported ∧
  decoderKind "fof(a,axiom,$$foo(a))." = some .unsupported ∧
  framerKind "fof(a,axiom,p($$c))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p($$c))." = some .unsupported ∧
  framerKind "fof(a,axiom,p(`X))." = some .unsupported ∧
  decoderKind "fof(a,axiom,p(`X))." = some .invalid ∧
  framerKind "fof(a,axiom,$fof(p))." = some .invalid ∧
  decoderKind "fof(a,axiom,$fof(p))." = some .unsupported ∧
  framerKind "tff(a,axiom,p)." = some .unsupported ∧
  decoderKind "tff(a,axiom,p)." = some .unsupported ∧
  framerKind "thf(a,axiom,p)." = some .unsupported ∧
  decoderKind "thf(a,axiom,p)." = some .unsupported ∧
  framerKind "tcf(a,axiom,p)." = some .unsupported ∧
  decoderKind "tcf(a,axiom,p)." = some .unsupported ∧
  framerKind "tpi(a,axiom,p)." = some .unsupported ∧
  decoderKind "tpi(a,axiom,p)." = some .invalid ∧
  framerKind "fof(a,axiom,[p] --> [q])." = some .unsupported ∧
  decoderKind "fof(a,axiom,[p] --> [q])." = some .invalid := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.NumericAudit.audit_other

end Fang.TptpCandidate.FullFof.Coverage.NumericAudit
