/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import QuotedAtom
import TermRendering

namespace Fang.TstpText.Controls

theorem escaped_quote_and_slash :
    (TstpExport.quote "Pietro's\\proof.p").toOption = some "'Pietro\\'s\\\\proof.p'" := by
  decide +kernel

theorem empty_label_rejected : (TstpExport.quote "").toOption = none := by decide +kernel

theorem newline_label_rejected : (TstpExport.quote "a\nb").toOption = none := by decide +kernel

theorem nonascii_label_rejected : (TstpExport.quote "caf\u00e9").toOption = none := by decide +kernel

theorem bare_quote_rejected : unquote "'a'b'" = none := by decide +kernel

theorem unknown_escape_rejected : unquote "'a\\qb'" = none := by decide +kernel

theorem ordered_nested_term :
    (TstpExport.term [⟨"f", some 2⟩, ⟨"a", some 0⟩]
      (.app 0 [.app 1 [], .var 17])).toOption = some "f(a,X17)" := by decide +kernel

theorem wrong_arity_rejected :
    (TstpExport.term [⟨"f", some 1⟩, ⟨"a", some 0⟩]
      (.app 0 [.app 1 [], .var 17])).toOption = none := by decide +kernel

end Fang.TstpText.Controls
