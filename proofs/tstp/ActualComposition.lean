/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license; see LICENSE. -/
import NamedSemantics
import Derivation

namespace Fang.TstpText

theorem related_last {relation : α → β → Prop} {left : List α} {right : List β}
    (h : Source.RelatedLists relation left right) {last : α}
    (found : left.getLast? = some last) :
    ∃ output, right.getLast? = some output ∧ relation last output := by
  induction h with
  | nil => simp at found
  | @cons first output rest outputs head tail ih =>
    cases rest with
    | nil =>
      cases tail
      have same : first = last := by simpa using found
      subst last
      exact ⟨output, by simp, head⟩
    | cons next remaining =>
      cases tail with
      | cons nextHead nextTail =>
        obtain ⟨lastOutput, lastFound, related⟩ := ih (by simpa using found)
        exact ⟨lastOutput, by simpa using lastFound, related⟩

theorem rendered_final_false {problem : TstpExport.NamedProblem}
    {certificate : Certificate} {exported : TstpExport.Export} {text : String}
    (fileLabel : String)
    (built : TstpExport.build problem certificate = .ok exported)
    (rendered : TstpExport.render fileLabel exported = .ok text) :
    ∃ lines, text = String.join lines ∧
      Source.RelatedLists (RowCorrespondence exported.signature fileLabel) exported.rows lines ∧
      (∃ lastLine role metadata, lines.getLast? = some lastLine ∧
        AnnotatedRowText lastLine exported.finalName role [] metadata) ∧
      text.utf8ByteSize ≤ 16 * 1024 * 1024 := by
  obtain ⟨lines, joined, rows, size⟩ := render_correspondence fileLabel exported rendered
  obtain ⟨_, finalName, finalClause⟩ := TstpExport.build_endpoint built
  cases final : exported.rows.getLast? with
  | none => simp [final] at finalClause
  | some row =>
    have empty : row.clause = [] := by simpa [final] using finalClause
    have name : row.name = exported.finalName := by simpa [final] using finalName
    obtain ⟨lastLine, lastFound, named, metadata, clause, _, grammar⟩ := related_last rows final
    have namedEmpty : named = [] := by
      rw [empty] at clause
      cases clause
      rfl
    refine ⟨lines, joined, rows, ⟨lastLine, originRole row.origin, metadata, lastFound, ?_⟩, size⟩
    simpa [name, namedEmpty] using grammar

/-- The premise is now actual decoding/building/rendering. The frozen builder
proof supplies Derivation, and named semantics uses the original source model. -/
theorem built_render_original_models {input : String} {problem : TstpExport.NamedProblem}
    {certificate : Certificate} {exported : TstpExport.Export} {text : String}
    (fileLabel : String)
    (decoded : TstpExport.decodeNamed input = .ok problem)
    (built : TstpExport.build problem certificate = .ok exported)
    (rendered : TstpExport.render fileLabel exported = .ok text) :
    TstpExport.Derivation exported.signature exported.rows ∧
    ∃ original, Source.Grammar.Parses (Source.Grammar.spelling input) original ∧
      ∀ (D : Type) (model : Source.Interpretation D), original.Models model →
        ∃ lines, text = String.join lines ∧
          Source.RelatedLists (SemanticRow exported.signature fileLabel model)
            exported.rows lines ∧ text.utf8ByteSize ≤ 16 * 1024 * 1024 := by
  have signature := (TstpExport.build_endpoint built).1
  have typed := TstpExport.BuilderProof.decoded_build_derivation input problem certificate exported decoded built
  have derivation : TstpExport.Derivation exported.signature exported.rows := by
    simpa [signature] using typed
  have decoded' : TstpExport.decodeNamed input = .ok exported.signature := by
    simpa [signature] using decoded
  exact ⟨derivation, render_original_models fileLabel exported decoded' rendered derivation⟩

/-- Actual export success produces an independently justified typed derivation
and text with the intended row fields and an empty final clause. Unique
full-text decoding, numeric origin IDs and minimal pruning remain separate. -/
theorem export_text_correspondence {input proof fileLabel text : String}
    (accepted : TstpExport.exportText input proof fileLabel = .ok text) :
    ∃ exported : TstpExport.Export,
      TstpExport.Derivation exported.signature exported.rows ∧
      (∃ lines, text = String.join lines ∧
        Source.RelatedLists (RowCorrespondence exported.signature fileLabel) exported.rows lines ∧
        (∃ lastLine role metadata, lines.getLast? = some lastLine ∧
          AnnotatedRowText lastLine exported.finalName role [] metadata) ∧
        text.utf8ByteSize ≤ 16 * 1024 * 1024) ∧
      (∃ original, Source.Grammar.Parses (Source.Grammar.spelling input) original ∧
        ∀ (D : Type) (model : Source.Interpretation D), original.Models model →
          ∃ lines, text = String.join lines ∧
            Source.RelatedLists (SemanticRow exported.signature fileLabel model)
              exported.rows lines ∧ text.utf8ByteSize ≤ 16 * 1024 * 1024) := by
  cases decoded : TstpExport.decodeNamed input with
  | error e => simp [TstpExport.exportText, decoded, bind, Except.bind] at accepted
  | ok problem =>
    cases certificate : decodeCertificate proof with
    | error e => simp [TstpExport.exportText, decoded, certificate, bind, Except.bind] at accepted
    | ok cert =>
      cases built : TstpExport.build problem cert with
      | error e => simp [TstpExport.exportText, decoded, certificate, built, bind, Except.bind] at accepted
      | ok exported =>
        have rendered : TstpExport.render fileLabel exported = .ok text := by
          simpa [TstpExport.exportText, decoded, certificate, built, bind, Except.bind] using accepted
        obtain ⟨derivation, semantics⟩ :=
          built_render_original_models fileLabel decoded built rendered
        exact ⟨exported, derivation, rendered_final_false fileLabel built rendered, semantics⟩

end Fang.TstpText
