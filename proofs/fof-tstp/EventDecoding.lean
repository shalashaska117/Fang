/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.EventParents

namespace Fang.FofTstpExport.RenderProof
open FofTstpText TstpText

inductive EventMeaning (problem : TstpExport.NamedProblem) (label : String) :
    Event → MixedRow → Prop where
  | inherited {row named metadata}
      (clause : NamedClause problem row.clause named)
      (source : SourceMeaning problem label row.origin metadata) :
      EventMeaning problem label (.inherited row)
        (.cnf ⟨row.name, originRole row.origin, named, metadata⟩)
  | source {index name body named} (formula : NamedFormula problem body named) :
      EventMeaning problem label (.source index name body)
        (.fof name named (.function "file" [.atom label, .atom name]))
  | clausify {leaf named} (clause : NamedClause problem leaf.clause named) :
      EventMeaning problem label (.clausify leaf)
        (.cnf ⟨leaf.rawName, .plain, named, clausificationData leaf⟩)

theorem event_text_decode {problem label event text}
    (meaning : EventText problem label event text) :
    ∃ parsed, MixedRowText text parsed ∧ EventMeaning problem label event parsed := by
  cases event with
  | inherited row =>
    obtain ⟨named, metadata, clause, source, grammar⟩ := meaning
    exact ⟨.cnf ⟨row.name, originRole row.origin, named, metadata⟩, grammar, .inherited clause source⟩
  | source index name body =>
    obtain ⟨named, formula, grammar⟩ := meaning
    exact ⟨.fof name named (.function "file" [.atom label, .atom name]), grammar, .source formula⟩
  | clausify leaf =>
    obtain ⟨named, clause, grammar⟩ := meaning
    exact ⟨.cnf ⟨leaf.rawName, .plain, named, clausificationData leaf⟩, grammar, .clausify clause⟩

theorem events_text_decode {problem label events texts}
    (meanings : Source.RelatedLists (EventText problem label) events texts) :
    ∃ parsed, Source.RelatedLists MixedRowText texts parsed ∧
      Source.RelatedLists (EventMeaning problem label) events parsed := by
  induction meanings with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons head tail ih =>
    obtain ⟨first, grammar, meaning⟩ := event_text_decode head
    obtain ⟨rest, remaining, meanings⟩ := ih
    exact ⟨first :: rest, .cons grammar remaining, .cons meaning meanings⟩

/-- One parsed sequence carries the same event witnesses as the actual renderer
    and its justified inference history. All bytes are consumed; a second full
    parse has exactly the same row fields. -/
theorem decoded_render_unique_derivation {input : String} {decoded : FOFFrontend.Decoded}
    (decodedOk : FOFFrontend.decode input = .ok decoded)
    {certificate : Certificate} {exported : Export}
    (built : build decoded certificate = .ok exported)
    {label text : String} (printed : render label exported = .ok text) :
    ∃ seen events texts parsed, text = String.join texts ∧
      TraceEvents exported exported.trace.rows [] seen events ∧
      Source.RelatedLists (EventMeaning exported.trace.signature label) events parsed ∧
      SourcesBefore [] events ∧
      (∀ event ∈ events, OriginalEvent decoded event) ∧
      EventDerivation exported.trace.signature exported events ∧
      ParsedMixedRows text.toList parsed ∧
      (∀ other, ParsedMixedRows text.toList other → other = parsed) := by
  obtain ⟨seen, events, texts, same, trace, meanings, sources, originals, derived⟩ :=
    decoded_render_derivation decodedOk built printed
  obtain ⟨parsed, grammar, correspondence⟩ := events_text_decode meanings
  have full : ParsedMixedRows text.toList parsed := by
    rw [same]
    exact mixed_rows_parse grammar
  exact ⟨seen, events, texts, parsed, same, trace, correspondence, sources, originals, derived,
    full, fun _ other => other.unique full⟩

theorem export_text_unique_derivation {input proof label text : String}
    (accepted : exportText input proof label = .ok text) :
    ¬ FOFGrammar.BytesSatisfiable (Source.Grammar.spelling input) ∧
    ∃ decoded certificate exported seen events texts parsed,
      FOFFrontend.decode input = .ok decoded ∧ FOFVersioned.decodeCertificate proof = .ok certificate ∧
      build decoded certificate = .ok exported ∧ render label exported = .ok text ∧
      text = String.join texts ∧
      TraceEvents exported exported.trace.rows [] seen events ∧
      Source.RelatedLists (EventMeaning exported.trace.signature label) events parsed ∧
      SourcesBefore [] events ∧
      (∀ event ∈ events, OriginalEvent decoded event) ∧
      EventDerivation exported.trace.signature exported events ∧
      ParsedMixedRows text.toList parsed ∧
      (∀ other, ParsedMixedRows text.toList other → other = parsed) := by
  refine ⟨export_original_unsat accepted, ?_⟩
  cases decodedOk : FOFFrontend.decode input with
  | error reason => simp [exportText, decodedOk, bind, Except.bind] at accepted
  | ok decoded =>
    cases certificateOk : FOFVersioned.decodeCertificate proof with
    | error reason => simp [exportText, decodedOk, certificateOk, bind, Except.bind] at accepted
    | ok certificate =>
      cases built : build decoded certificate with
      | error reason => simp [exportText, decodedOk, certificateOk, built, bind, Except.bind] at accepted
      | ok exported =>
        have printed : render label exported = .ok text := by
          simpa [exportText, decodedOk, certificateOk, built, bind, Except.bind] using accepted
        obtain ⟨seen, events, texts, parsed, rest⟩ := decoded_render_unique_derivation decodedOk built printed
        exact ⟨decoded, certificate, exported, seen, events, texts, parsed,
          rfl, rfl, built, printed, rest⟩

end Fang.FofTstpExport.RenderProof
