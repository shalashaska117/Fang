/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import ActualComposition
import ExportProvenance

namespace Fang.TstpText

open TstpExport.BuilderProof

theorem rows_provenance {problem : TstpExport.NamedProblem} {certificate : Certificate}
    {clauses : List Clause} {rows : List TstpExport.Row} {lines : List String} {label : String}
    (correspondence : Source.RelatedLists (RowCorrespondence problem label) rows lines)
    (origins : CertificateRows problem certificate clauses rows)
    (relevant : ∀ row ∈ rows, RowReachable certificate row) :
    Source.RelatedLists (fun row line =>
      RowCorrespondence problem label row line ∧
      CertificateRow problem certificate clauses row ∧ RowReachable certificate row) rows lines := by
  induction correspondence with
  | nil => exact .nil
  | @cons row line rows lines first rest ih =>
    exact .cons ⟨first, origins row (by simp), relevant row (by simp)⟩
      (ih (fun row member => origins row (List.mem_cons_of_mem _ member))
          (fun row member => relevant row (List.mem_cons_of_mem _ member)))

/-- Printed metadata is tied to the actual decoded certificate and checked
trace, and every row belongs to the final node's backward-reachable graph.
This does not claim minimality or unique text decoding. -/
theorem export_traced_rows {input proof label text : String}
    (accepted : TstpExport.exportText input proof label = .ok text) :
    ∃ problem certificate output clauses lines,
      TstpExport.decodeNamed input = .ok problem ∧ decodeCertificate proof = .ok certificate ∧
      TstpExport.build problem certificate = .ok output ∧
      TstpExport.render label output = .ok text ∧ output.signature = problem ∧
      TstpExport.Derivation problem output.rows ∧
      checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses ∧
      text = String.join lines ∧
      Source.RelatedLists (fun row line =>
        RowCorrespondence problem label row line ∧
        CertificateRow problem certificate clauses row ∧ RowReachable certificate row) output.rows lines ∧
      (∃ lastLine role metadata, lines.getLast? = some lastLine ∧
        AnnotatedRowText lastLine output.finalName role [] metadata) ∧
      text.utf8ByteSize ≤ 16 * 1024 * 1024 := by
  obtain ⟨problem, certificate, output, clauses, decoded, decodedProof, built,
    rendered, signature, derivation, trace, origins, relevant⟩ := export_provenance accepted
  obtain ⟨lines, joined, correspondence, final, size⟩ := rendered_final_false label built rendered
  have same : Source.RelatedLists (RowCorrespondence problem label) output.rows lines := by
    simpa [signature] using correspondence
  exact ⟨problem, certificate, output, clauses, lines, decoded, decodedProof, built, rendered,
    signature, derivation, trace, joined, rows_provenance same origins relevant, final, size⟩

end Fang.TstpText
