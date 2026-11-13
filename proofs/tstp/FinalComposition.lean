/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import ProvenanceComposition
import SequenceUniqueness
import LeafText

namespace Fang.TstpText

open TstpExport.BuilderProof

theorem rows_original_semantics {input : String} {problem : TstpExport.NamedProblem}
    {label rows lines}
    (decoded : TstpExport.decodeNamed input = .ok problem)
    (derivation : TstpExport.Derivation problem rows)
    (correspondence : Source.RelatedLists (RowCorrespondence problem label) rows lines) :
    ∃ original, Source.Grammar.Parses (Source.Grammar.spelling input) original ∧
      ∀ (D : Type) (model : Source.Interpretation D), original.Models model →
        Source.RelatedLists (SemanticRow problem label model) rows lines := by
  obtain ⟨original, state, parsed, encoding, functions, predicates, _⟩ :=
    TstpExport.decodeNamed_source decoded
  refine ⟨original, parsed, ?_⟩
  intro D model models
  apply rows_semantics correspondence model
  apply TstpExport.derivation_valid _ _ _ ?_ derivation
  have same : tableModel problem model = model.toNumeric (Frontend.symbolsFrom state) := by
    simp [tableModel, Source.Interpretation.toNumeric, Frontend.symbolsFrom, functions, predicates]
  rw [same]
  intro clause member
  obtain ⟨named, namedMember, variables, relation⟩ := encoding.clauses.member_right member
  exact relation.valid_toNumeric model (models named namedMember)

theorem rows_with_leaves {input : String} {problem : TstpExport.NamedProblem}
    {certificate : Certificate} {output : TstpExport.Export} {label : String}
    {clauses : List Clause} {lines : List String}
    (decoded : TstpExport.decodeNamed input = .ok problem)
    (built : TstpExport.build problem certificate = .ok output)
    (traced : Source.RelatedLists (fun row line =>
      RowCorrespondence problem label row line ∧
      CertificateRow problem certificate clauses row ∧ RowReachable certificate row) output.rows lines) :
    Source.RelatedLists (fun row line =>
      RowCorrespondence problem label row line ∧
      CertificateRow problem certificate clauses row ∧ RowReachable certificate row ∧
      RawLeafText input problem label row line) output.rows lines := by
  have signature := (TstpExport.build_endpoint built).1
  have strengthen : ∀ rows lines,
      Source.RelatedLists (fun row line => RowCorrespondence problem label row line ∧
        CertificateRow problem certificate clauses row ∧ RowReachable certificate row) rows lines →
      (∀ row ∈ rows, row ∈ output.rows) →
      Source.RelatedLists (fun row line => RowCorrespondence problem label row line ∧
        CertificateRow problem certificate clauses row ∧ RowReachable certificate row ∧
        RawLeafText input problem label row line) rows lines := by
    intro rows lines relation
    induction relation with
    | nil => intro _; exact .nil
    | @cons row line rows lines head tail ih =>
      intro members
      have correspondence : RowCorrespondence output.signature label row line := by
        simpa [signature] using head.1
      exact .cons ⟨head.1, head.2.1, head.2.2,
        built_row_alpha decoded built (members _ (by simp)) correspondence⟩
        (ih (fun row member => members row (List.mem_cons_of_mem _ member)))
  exact strengthen _ _ traced (fun _ member => member)

theorem traced_correspondence {problem label certificate clauses rows lines}
    (traced : Source.RelatedLists (fun row line =>
      RowCorrespondence problem label row line ∧
      CertificateRow problem certificate clauses row ∧ RowReachable certificate row) rows lines) :
    Source.RelatedLists (RowCorrespondence problem label) rows lines := by
  induction traced with
  | nil => exact .nil
  | cons head tail ih => exact .cons head.1 ih

/-- The actual unchanged exporter yields one uniquely decoded ordered proof
text. The same row witnesses carry source leaves, checked certificate fields,
graph relevance, original-model validity and the final empty clause. This
statement concerns the Lean definitions, not compiled execution. -/
theorem export_complete_text {input proof label text : String}
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
      text.utf8ByteSize ≤ 16 * 1024 * 1024 := by
  obtain ⟨problem, certificate, output, clauses, lines, decoded, decodedProof, built,
    rendered, signature, derivation, trace, joined, traced, final, size⟩ :=
    export_traced_rows accepted
  have correspondence := traced_correspondence traced
  obtain ⟨printed, grammar, named⟩ := correspondence_printed_rows correspondence
  have parsed : ParsedRows text.toList printed := by
    rw [joined]
    exact printed_rows_parse grammar
  obtain ⟨original, originalParsed, semantics⟩ :=
    rows_original_semantics decoded derivation correspondence
  exact ⟨problem, certificate, output, clauses, lines, printed, original,
    decoded, decodedProof, built, rendered, signature, derivation, trace, joined,
    rows_with_leaves decoded built traced, grammar, named, parsed,
    fun _ other => other.unique parsed, originalParsed, semantics, final, size⟩

end Fang.TstpText
