/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Controls for the symbol printer of the refutation exporters. A lower word
   prints as it is, every other nonempty printable name as a single-quoted atom
   with quote and backslash escaped, and a name that no atomic word spells is an
   export error. The names are of the kinds that did not print before: a lower
   word with upper-case letters, an upper-case name and a digit name. -/
import EqualityBody
import EqualityFormulaText

namespace Fang.TstpText.SymbolControls
open Fang.QuantifiedEqualityTstp

def objectName : String := String.ofList [Char.ofNat 0, 'o', 'b', 'j']

def functions : List Frontend.Symbol :=
  [⟨"E", some 0⟩, ⟨"aNaturalNumber0", some 1⟩, ⟨"0", some 0⟩, ⟨"LE", some 2⟩, ⟨"it's", some 0⟩,
   ⟨"a\\b", some 0⟩, ⟨objectName, some 0⟩, ⟨"", some 0⟩, ⟨"ssNder1_0", some 0⟩, ⟨"é", some 0⟩]

theorem quoted_upper : TstpExport.symbol functions 0 0 = .ok "'E'" := by decide +kernel
theorem lower_word_mixed : TstpExport.symbol functions 1 1 = .ok "aNaturalNumber0" := by decide +kernel
theorem quoted_digit : TstpExport.symbol functions 2 0 = .ok "'0'" := by decide +kernel
theorem quoted_quote : TstpExport.symbol functions 4 0 = .ok "'it\\'s'" := by decide +kernel
theorem quoted_backslash : TstpExport.symbol functions 5 0 = .ok "'a\\\\b'" := by decide +kernel
theorem lower_word_digits : TstpExport.symbol functions 8 0 = .ok "ssNder1_0" := by decide +kernel
theorem object_rejected :
    TstpExport.symbol functions 6 0 = .error "export-error: symbol name or arity mismatch" := by decide +kernel
theorem empty_rejected :
    TstpExport.symbol functions 7 0 = .error "export-error: symbol name or arity mismatch" := by decide +kernel
theorem nonascii_rejected :
    TstpExport.symbol functions 9 0 = .error "export-error: symbol name or arity mismatch" := by decide +kernel
theorem arity_rejected :
    TstpExport.symbol functions 1 0 = .error "export-error: symbol name or arity mismatch" := by decide +kernel
theorem unknown_rejected :
    TstpExport.symbol functions 10 0 = .error "export-error: unknown symbol" := by decide +kernel

def mixed : Fang.Term := .app 3 [.app 0 [], .app 1 [.var 2]]

theorem term_control : TstpExport.term functions mixed = .ok "'LE'('E',aNaturalNumber0(X2))" := by decide +kernel

/-- The printed term reads back as the term over the table names. -/
theorem term_reads : ∃ named, NamedTerm functions mixed named ∧
    TermBytesParse (Source.Grammar.spelling "'LE'('E',aNaturalNumber0(X2))") named :=
  term_byte_correspondence mixed term_control

def names : Body.Names := ⟨functions, [⟨"P", some 1⟩, ⟨"less", some 2⟩]⟩

theorem literal_control :
    Body.literal names ⟨false, .predicate ⟨1, [.app 2 [], .app 0 []]⟩⟩ = .ok "~less('0','E')" := by decide +kernel
theorem equality_control :
    Body.literal names ⟨true, .equal (.app 0 []) (.app 1 [.app 2 []])⟩ = .ok "'E' = aNaturalNumber0('0')" := by
  decide +kernel
theorem clause_control :
    Body.clause names [⟨true, .predicate ⟨0, [.var 1]⟩⟩, ⟨false, .equal (.var 1) (.app 0 [])⟩] =
      .ok "'P'(X1) | X1 != 'E'" := by decide +kernel

theorem group_formula_control :
    FormulaText.render (.all "X1" (.disj (.atom (.predicate "P" [.var "X1"])) (.neg (.atom (.equal (.var "X1") (.app "E" []))))))
      = .ok "! [ X1 ] : ( ( 'P' ( X1 ) ) | ~ ( X1 = 'E' ) )" := rfl

#print axioms Fang.TstpText.SymbolControls.quoted_upper
#print axioms Fang.TstpText.SymbolControls.lower_word_mixed
#print axioms Fang.TstpText.SymbolControls.quoted_digit
#print axioms Fang.TstpText.SymbolControls.quoted_quote
#print axioms Fang.TstpText.SymbolControls.quoted_backslash
#print axioms Fang.TstpText.SymbolControls.lower_word_digits
#print axioms Fang.TstpText.SymbolControls.object_rejected
#print axioms Fang.TstpText.SymbolControls.empty_rejected
#print axioms Fang.TstpText.SymbolControls.nonascii_rejected
#print axioms Fang.TstpText.SymbolControls.arity_rejected
#print axioms Fang.TstpText.SymbolControls.unknown_rejected
#print axioms Fang.TstpText.SymbolControls.term_control
#print axioms Fang.TstpText.SymbolControls.term_reads
#print axioms Fang.TstpText.SymbolControls.literal_control
#print axioms Fang.TstpText.SymbolControls.equality_control
#print axioms Fang.TstpText.SymbolControls.clause_control
#print axioms Fang.TstpText.SymbolControls.group_formula_control

end Fang.TstpText.SymbolControls
