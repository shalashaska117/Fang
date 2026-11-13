/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import FinalComposition

open Fang Fang.TstpText Fang.TstpExport.BuilderProof

example {input proof label text : String}
    (accepted : TstpExport.exportText input proof label = .ok text) :
    ∃ problem certificate output clauses lines printed original,
      TstpExport.decodeNamed input = .ok problem ∧ decodeCertificate proof = .ok certificate ∧
      TstpExport.build problem certificate = .ok output ∧
      TstpExport.render label output = .ok text ∧ output.signature = problem ∧
      TstpExport.Derivation problem output.rows ∧
      checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses ∧
      text = String.join lines ∧
      Source.RelatedLists (fun row line =>
        RowCorrespondence problem label row line ∧
        CertificateRow problem certificate clauses row ∧ RowReachable certificate row ∧
        RawLeafText input problem label row line) output.rows lines ∧
      Source.RelatedLists PrintedRowText lines printed ∧
      Source.RelatedLists (fun row named =>
        named.name = row.name ∧ named.role = originRole row.origin ∧
        NamedClause problem row.clause named.clause ∧
        SourceMeaning problem label row.origin named.metadata) output.rows printed ∧
      ParsedRows text.toList printed ∧
      (∀ other, ParsedRows text.toList other → other = printed) ∧
      Source.Grammar.Parses (Source.Grammar.spelling input) original ∧
      (∀ (D : Type) (model : Source.Interpretation D), original.Models model →
        Source.RelatedLists (SemanticRow problem label model) output.rows lines) ∧
      (∃ lastLine role metadata, lines.getLast? = some lastLine ∧
        AnnotatedRowText lastLine output.finalName role [] metadata) ∧
      text.utf8ByteSize ≤ 16 * 1024 * 1024 := export_complete_text accepted

#print axioms Fang.TstpText.rows_original_semantics
#print axioms Fang.TstpText.rows_with_leaves
#print axioms Fang.TstpText.export_complete_text
