/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import QuotedAtom
import TermRendering
import Controls
import VariableNames
import TermParsing
import LiteralParsing
import ClauseParsing
import NamedSemantics
import ActualComposition
import ProvenanceComposition
import AnnotationGrammar
import WitnessMetadata
import SourceMetadata
import AnnotatedRows

example {input output : String} (accepted : Fang.TstpExport.quote input = .ok output) :
    Fang.TstpText.QuotedAtom output.toList input.toList :=
  Fang.TstpText.quote_grammar accepted

example {code payload : List Char} (h : Fang.TstpText.QuotedAtom code payload) :
    Fang.TstpText.decodeQuoted code = some payload := Fang.TstpText.decodeQuoted_correct h

example {code left right : List Char} (hl : Fang.TstpText.QuotedAtom code left)
    (hr : Fang.TstpText.QuotedAtom code right) : left = right := hl.functional hr

example {input output : String} (h : Fang.TstpExport.quote input = .ok output) :
    Fang.TstpText.unquote output = some input := Fang.TstpText.quote_roundtrip h

example {input output : String} (h : Fang.TstpExport.quote input = .ok output) :
    String.toUTF8 <$> Fang.TstpText.unquote output = some input.toUTF8 :=
  Fang.TstpText.quote_utf8_roundtrip h

example {left right output : String} (hl : Fang.TstpExport.quote left = .ok output)
    (hr : Fang.TstpExport.quote right = .ok output) : left = right :=
  Fang.TstpText.quote_injective hl hr

example {symbols : List Fang.Frontend.Symbol} {index arity : Nat} {name : String}
    (h : Fang.TstpExport.symbol symbols index arity = .ok name) :
    Fang.TstpText.SymbolText symbols index arity name := Fang.TstpText.symbol_correspondence h

example {symbols : List Fang.Frontend.Symbol} (value : Fang.Term) {text : String}
    (h : Fang.TstpExport.term symbols value = .ok text) :
    Fang.TstpText.TermText symbols value text := Fang.TstpText.term_correspondence value h

example {symbols : List Fang.Frontend.Symbol} (values : List Fang.Term) {texts : List String}
    (h : Fang.TstpExport.terms symbols values = .ok texts) :
    Fang.TstpText.TermsText symbols values texts := Fang.TstpText.terms_correspondence values h

example {problem : Fang.TstpExport.NamedProblem} (value : Fang.Literal) {text : String}
    (h : Fang.TstpExport.literal problem value = .ok text) :
    Fang.TstpText.LiteralText problem value text := Fang.TstpText.literal_correspondence value h

#print axioms Fang.TstpText.quote_grammar
#print axioms Fang.TstpText.decodeQuoted_correct
#print axioms Fang.TstpText.QuotedAtom.functional
#print axioms Fang.TstpText.quote_roundtrip
#print axioms Fang.TstpText.quote_utf8_roundtrip
#print axioms Fang.TstpText.quote_injective
#print axioms Fang.TstpText.symbol_correspondence
#print axioms Fang.TstpText.term_correspondence
#print axioms Fang.TstpText.terms_correspondence
#print axioms Fang.TstpText.literal_correspondence

example (index : Nat) : Fang.Frontend.variableName s!"X{index}" = true :=
  Fang.TstpText.variable_name_valid index
example (index : Nat) : Fang.Source.Grammar.VariableName s!"X{index}" :=
  Fang.TstpText.variable_name_grammar index
example {left right : Nat} (h : s!"X{left}" = s!"X{right}") : left = right :=
  Fang.TstpText.variable_name_injective h

#print axioms Fang.TstpText.variable_name_valid
#print axioms Fang.TstpText.variable_name_grammar
#print axioms Fang.TstpText.variable_name_injective

example {bytes left right} (hl : Fang.TstpText.TermBytesParse bytes left)
    (hr : Fang.TstpText.TermBytesParse bytes right) : left = right := hl.unique hr
example {symbols : List Fang.Frontend.Symbol} (value : Fang.Term) {text : String}
    (accepted : Fang.TstpExport.term symbols value = .ok text) :
    ∃ named, Fang.TstpText.NamedTerm symbols value named ∧
      Fang.TstpText.TermBytesParse (Fang.Source.Grammar.spelling text) named :=
  Fang.TstpText.term_byte_correspondence value accepted

#print axioms Fang.TstpText.TermBytesParse.unique
#print axioms Fang.TstpText.term_byte_correspondence

example {bytes left right} (hl : Fang.TstpText.LiteralBytesParse bytes left)
    (hr : Fang.TstpText.LiteralBytesParse bytes right) : left = right := hl.unique hr
example {problem : Fang.TstpExport.NamedProblem} (value : Fang.Literal) {text : String}
    (accepted : Fang.TstpExport.literal problem value = .ok text) :
    ∃ named, Fang.TstpText.NamedLiteral problem value named ∧
      Fang.TstpText.LiteralBytesParse (Fang.Source.Grammar.spelling text) named :=
  Fang.TstpText.literal_byte_correspondence value accepted

#print axioms Fang.TstpText.LiteralBytesParse.unique
#print axioms Fang.TstpText.literal_byte_correspondence

example {bytes left right} (hl : Fang.TstpText.ClauseBytesParse bytes left)
    (hr : Fang.TstpText.ClauseBytesParse bytes right) : left = right := hl.unique hr
example {problem : Fang.TstpExport.NamedProblem} (value : Fang.Clause) {text : String}
    (accepted : Fang.TstpExport.clause problem value = .ok text) :
    ∃ named, Fang.TstpText.NamedClause problem value named ∧
      Fang.TstpText.ClauseBytesParse (Fang.Source.Grammar.spelling text) named :=
  Fang.TstpText.clause_byte_correspondence value accepted

#print axioms Fang.TstpText.ClauseBytesParse.unique
#print axioms Fang.TstpText.clause_byte_correspondence

example (index : Nat) : Fang.TstpText.NaturalSpelling (toString index).toList index :=
  Fang.TstpText.natural_spelling index
example {chars left right} (hl : Fang.TstpText.NaturalSpelling chars left)
    (hr : Fang.TstpText.NaturalSpelling chars right) : left = right := hl.functional hr

#print axioms Fang.TstpText.natural_spelling
#print axioms Fang.TstpText.NaturalSpelling.functional

example {symbols : List Fang.Frontend.Symbol} (value : Fang.Term) {text : String}
    (h : Fang.TstpExport.witnessTerm symbols value = .ok text) :
    ∃ named, Fang.TstpText.WitnessMeaning symbols value named ∧ Fang.TstpText.DataText text named :=
  Fang.TstpText.witness_term_correspondence value h
example {symbols : List Fang.Frontend.Symbol} (values : List Fang.Term) {texts : List String}
    (h : Fang.TstpExport.witnessTerms symbols values = .ok texts) :
    ∃ named, Fang.TstpText.WitnessesMeaning symbols values named ∧ Fang.TstpText.DataTexts texts named :=
  Fang.TstpText.witness_terms_correspondence values h
example {problem : Fang.TstpExport.NamedProblem} (substitution : Fang.Subst) {text : String}
    (h : Fang.TstpExport.witness problem substitution = .ok text) :
    ∃ bindings, Fang.TstpText.BindingsMeaning problem.functions substitution bindings ∧
      Fang.TstpText.DataText text (.function "fang_substitution" [.list bindings]) :=
  Fang.TstpText.witness_correspondence substitution h

#print axioms Fang.TstpText.witness_term_correspondence
#print axioms Fang.TstpText.witness_terms_correspondence
#print axioms Fang.TstpText.witness_correspondence

example {problem : Fang.TstpExport.NamedProblem} (label : String) (origin : Fang.TstpExport.Origin)
    {text : String} (h : Fang.TstpExport.source problem label origin = .ok text) :
    ∃ data, Fang.TstpText.SourceMeaning problem label origin data ∧ Fang.TstpText.DataText text data :=
  Fang.TstpText.source_correspondence label origin h
example {problem label origin data} (h : Fang.TstpText.SourceMeaning problem label origin data) :
    Fang.TstpText.SourceRecord data := h.record

#print axioms Fang.TstpText.source_correspondence
#print axioms Fang.TstpText.SourceMeaning.record

example {problem : Fang.TstpExport.NamedProblem} (label : String) (row : Fang.TstpExport.Row)
    {text : String} (h : Fang.TstpExport.renderRow problem label row = .ok text) :
    Fang.TstpText.RowCorrespondence problem label row text :=
  Fang.TstpText.row_correspondence label row h
example (label : String) (exported : Fang.TstpExport.Export) {text : String}
    (h : Fang.TstpExport.render label exported = .ok text) :
    ∃ lines, text = String.join lines ∧
      Fang.Source.RelatedLists (Fang.TstpText.RowCorrespondence exported.signature label)
        exported.rows lines ∧ text.utf8ByteSize ≤ 16 * 1024 * 1024 :=
  Fang.TstpText.render_correspondence label exported h

#print axioms Fang.TstpText.row_correspondence
#print axioms Fang.TstpText.render_correspondence

example {problem : Fang.TstpExport.NamedProblem} {value named}
    (h : Fang.TstpText.NamedTerm problem.functions value named) {D : Type}
    (model : Fang.Source.Interpretation D) (valuation : String → D) :
    named.eval model valuation =
      value.eval (Fang.TstpText.tableModel problem model) (fun index => valuation s!"X{index}") :=
  h.eval model valuation
example {problem : Fang.TstpExport.NamedProblem} {values named}
    (h : Fang.TstpText.NamedTerms problem.functions values named) {D : Type}
    (model : Fang.Source.Interpretation D) (valuation : String → D) :
    named.map (Fang.Source.Term.eval model valuation) =
      values.map (Fang.Term.eval (Fang.TstpText.tableModel problem model)
        (fun index => valuation s!"X{index}")) := h.eval model valuation
example {problem : Fang.TstpExport.NamedProblem} {value named}
    (h : Fang.TstpText.NamedLiteral problem value named) {D : Type}
    (model : Fang.Source.Interpretation D) (valuation : String → D) :
    named.Holds model valuation ↔
      value.Holds (Fang.TstpText.tableModel problem model) (fun index => valuation s!"X{index}") :=
  h.holds model valuation
example {problem : Fang.TstpExport.NamedProblem} {value named}
    (h : Fang.TstpText.NamedClause problem value named) {D : Type}
    (model : Fang.Source.Interpretation D) (name : String)
    (valid : value.Valid (Fang.TstpText.tableModel problem model)) :
    (Fang.Source.Clause.mk name named).Valid model := h.valid model name valid
example (fileLabel : String) (exported : Fang.TstpExport.Export) {text : String}
    (rendered : Fang.TstpExport.render fileLabel exported = .ok text)
    (derivation : Fang.TstpExport.Derivation exported.signature exported.rows)
    {D : Type} (model : Fang.Source.Interpretation D)
    (original : exported.signature.signature.problem.Models
      (Fang.TstpText.tableModel exported.signature model)) :
    ∃ lines, text = String.join lines ∧
      Fang.Source.RelatedLists (Fang.TstpText.SemanticRow exported.signature fileLabel model)
        exported.rows lines ∧ text.utf8ByteSize ≤ 16 * 1024 * 1024 :=
  Fang.TstpText.render_derivation_valid fileLabel exported rendered derivation model original
example {input text : String} (fileLabel : String) (exported : Fang.TstpExport.Export)
    (decoded : Fang.TstpExport.decodeNamed input = .ok exported.signature)
    (rendered : Fang.TstpExport.render fileLabel exported = .ok text)
    (derivation : Fang.TstpExport.Derivation exported.signature exported.rows) :
    ∃ original, Fang.Source.Grammar.Parses (Fang.Source.Grammar.spelling input) original ∧
      ∀ (D : Type) (model : Fang.Source.Interpretation D), original.Models model →
        ∃ lines, text = String.join lines ∧
          Fang.Source.RelatedLists (Fang.TstpText.SemanticRow exported.signature fileLabel model)
            exported.rows lines ∧ text.utf8ByteSize ≤ 16 * 1024 * 1024 :=
  Fang.TstpText.render_original_models fileLabel exported decoded rendered derivation

#print axioms Fang.TstpText.NamedTerm.eval
#print axioms Fang.TstpText.NamedTerms.eval
#print axioms Fang.TstpText.NamedLiteral.holds
#print axioms Fang.TstpText.NamedClause.valid
#print axioms Fang.TstpText.render_derivation_valid
#print axioms Fang.TstpText.render_original_models

example {problem : Fang.TstpExport.NamedProblem}
    {certificate : Fang.Certificate} {exported : Fang.TstpExport.Export} {text : String}
    (fileLabel : String)
    (built : Fang.TstpExport.build problem certificate = .ok exported)
    (rendered : Fang.TstpExport.render fileLabel exported = .ok text) :
    ∃ lines, text = String.join lines ∧
      Fang.Source.RelatedLists (Fang.TstpText.RowCorrespondence exported.signature fileLabel)
        exported.rows lines ∧
      (∃ lastLine role metadata, lines.getLast? = some lastLine ∧
        Fang.TstpText.AnnotatedRowText lastLine exported.finalName role [] metadata) ∧
      text.utf8ByteSize ≤ 16 * 1024 * 1024 :=
  Fang.TstpText.rendered_final_false fileLabel built rendered
example {input : String} {problem : Fang.TstpExport.NamedProblem}
    {certificate : Fang.Certificate} {exported : Fang.TstpExport.Export} {text : String}
    (fileLabel : String) (decoded : Fang.TstpExport.decodeNamed input = .ok problem)
    (built : Fang.TstpExport.build problem certificate = .ok exported)
    (rendered : Fang.TstpExport.render fileLabel exported = .ok text) :
    Fang.TstpExport.Derivation exported.signature exported.rows ∧
    ∃ original, Fang.Source.Grammar.Parses (Fang.Source.Grammar.spelling input) original ∧
      ∀ (D : Type) (model : Fang.Source.Interpretation D), original.Models model →
        ∃ lines, text = String.join lines ∧
          Fang.Source.RelatedLists (Fang.TstpText.SemanticRow exported.signature fileLabel model)
            exported.rows lines ∧ text.utf8ByteSize ≤ 16 * 1024 * 1024 :=
  Fang.TstpText.built_render_original_models fileLabel decoded built rendered
example {input proof fileLabel text : String}
    (accepted : Fang.TstpExport.exportText input proof fileLabel = .ok text) :
    ∃ exported : Fang.TstpExport.Export,
      Fang.TstpExport.Derivation exported.signature exported.rows ∧
      (∃ lines, text = String.join lines ∧
        Fang.Source.RelatedLists (Fang.TstpText.RowCorrespondence exported.signature fileLabel)
          exported.rows lines ∧
        (∃ lastLine role metadata, lines.getLast? = some lastLine ∧
          Fang.TstpText.AnnotatedRowText lastLine exported.finalName role [] metadata) ∧
        text.utf8ByteSize ≤ 16 * 1024 * 1024) ∧
      (∃ original, Fang.Source.Grammar.Parses (Fang.Source.Grammar.spelling input) original ∧
        ∀ (D : Type) (model : Fang.Source.Interpretation D), original.Models model →
          ∃ lines, text = String.join lines ∧
            Fang.Source.RelatedLists (Fang.TstpText.SemanticRow exported.signature fileLabel model)
              exported.rows lines ∧ text.utf8ByteSize ≤ 16 * 1024 * 1024) :=
  Fang.TstpText.export_text_correspondence accepted

#print axioms Fang.TstpText.rendered_final_false
#print axioms Fang.TstpText.built_render_original_models
#print axioms Fang.TstpText.export_text_correspondence

example {input proof label text : String}
    (accepted : Fang.TstpExport.exportText input proof label = .ok text) :
    ∃ problem certificate output clauses lines,
      Fang.TstpExport.decodeNamed input = .ok problem ∧ Fang.decodeCertificate proof = .ok certificate ∧
      Fang.TstpExport.build problem certificate = .ok output ∧
      Fang.TstpExport.render label output = .ok text ∧ output.signature = problem ∧
      Fang.TstpExport.Derivation problem output.rows ∧
      Fang.checkSteps (Fang.preprocess problem.signature.problem) [] certificate.steps = some clauses ∧
      text = String.join lines ∧
      Fang.Source.RelatedLists (fun row line =>
        Fang.TstpText.RowCorrespondence problem label row line ∧
        Fang.TstpExport.BuilderProof.CertificateRow problem certificate clauses row ∧
        Fang.TstpExport.BuilderProof.RowReachable certificate row) output.rows lines ∧
      (∃ lastLine role metadata, lines.getLast? = some lastLine ∧
        Fang.TstpText.AnnotatedRowText lastLine output.finalName role [] metadata) ∧
      text.utf8ByteSize ≤ 16 * 1024 * 1024 :=
  Fang.TstpText.export_traced_rows accepted

#print axioms Fang.TstpText.export_traced_rows

example :
    (Fang.TstpExport.quote "Pietro's\\proof.p").toOption = some "'Pietro\\'s\\\\proof.p'" :=
  Fang.TstpText.Controls.escaped_quote_and_slash
example : (Fang.TstpExport.quote "").toOption = none := Fang.TstpText.Controls.empty_label_rejected
example : (Fang.TstpExport.quote "a\nb").toOption = none := Fang.TstpText.Controls.newline_label_rejected
example : (Fang.TstpExport.quote "caf\u00e9").toOption = none := Fang.TstpText.Controls.nonascii_label_rejected
example : Fang.TstpText.unquote "'a'b'" = none := Fang.TstpText.Controls.bare_quote_rejected
example : Fang.TstpText.unquote "'a\\qb'" = none := Fang.TstpText.Controls.unknown_escape_rejected
example :
    (Fang.TstpExport.term [⟨"f", some 2⟩, ⟨"a", some 0⟩]
      (.app 0 [.app 1 [], .var 17])).toOption = some "f(a,X17)" :=
  Fang.TstpText.Controls.ordered_nested_term
example :
    (Fang.TstpExport.term [⟨"f", some 1⟩, ⟨"a", some 0⟩]
      (.app 0 [.app 1 [], .var 17])).toOption = none :=
  Fang.TstpText.Controls.wrong_arity_rejected

#print axioms Fang.TstpText.Controls.escaped_quote_and_slash
#print axioms Fang.TstpText.Controls.empty_label_rejected
#print axioms Fang.TstpText.Controls.newline_label_rejected
#print axioms Fang.TstpText.Controls.nonascii_label_rejected
#print axioms Fang.TstpText.Controls.bare_quote_rejected
#print axioms Fang.TstpText.Controls.unknown_escape_rejected
#print axioms Fang.TstpText.Controls.ordered_nested_term
#print axioms Fang.TstpText.Controls.wrong_arity_rejected
