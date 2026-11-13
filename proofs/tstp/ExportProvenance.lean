/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import Leaves

namespace Fang.TstpExport.BuilderProof

/-- Expose the actual decoder/checker/builder witnesses behind successful text
    export. Text decoding and compiled execution remain separate boundaries. -/
theorem export_provenance {input proof fileLabel text : String}
    (accepted : exportText input proof fileLabel = .ok text) :
    ∃ problem certificate output clauses,
      decodeNamed input = .ok problem ∧ decodeCertificate proof = .ok certificate ∧
      build problem certificate = .ok output ∧ render fileLabel output = .ok text ∧
      output.signature = problem ∧ Derivation problem output.rows ∧
      checkSteps (preprocess problem.signature.problem) [] certificate.steps = some clauses ∧
      CertificateRows problem certificate clauses output.rows ∧
      ∀ row ∈ output.rows, RowReachable certificate row := by
  cases decoded : decodeNamed input with
  | error reason => simp [exportText, decoded, bind, Except.bind] at accepted
  | ok problem =>
    cases checkedCertificate : decodeCertificate proof with
    | error reason => simp [exportText, decoded, checkedCertificate, bind, Except.bind] at accepted
    | ok certificate =>
      cases built : build problem certificate with
      | error reason => simp [exportText, decoded, checkedCertificate, built, bind, Except.bind] at accepted
      | ok output =>
        have rendered : render fileLabel output = .ok text := by
          simpa [exportText, decoded, checkedCertificate, built, bind, Except.bind] using accepted
        obtain ⟨clauses, trace, origins⟩ := build_origins problem certificate output built
        exact ⟨problem, certificate, output, clauses, rfl, rfl, built, rendered,
          (build_endpoint built).1, decoded_build_derivation input problem certificate output decoded built,
          trace, origins, build_relevant problem certificate output built⟩

end Fang.TstpExport.BuilderProof
