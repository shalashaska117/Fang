/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft: not accepted until the next full proof gate. -/
import Fang.FOF.TSTP.OriginalFormulaRows

namespace Fang.FofTstpExport.RenderProof
open FofTstpText TstpText

def parsedName : MixedRow → String
  | .cnf row => row.name
  | .fof name _ _ => name

theorem EventMeaning.name_eq {problem label event parsed}
    (meaning : EventMeaning problem label event parsed) : parsedName parsed = event.name := by
  cases meaning <;> rfl

theorem event_meaning_names {problem label events parsed}
    (meanings : Source.RelatedLists (EventMeaning problem label) events parsed) :
    parsed.map parsedName = events.map Event.name := by
  induction meanings with
  | nil => rfl
  | cons head tail ih => simp [head.name_eq, ih]

/-- All fields refer to one parsed sequence and one actual expanded trace.
    This theorem covers the bounded ground FOF exporter, not quantified FOF,
    equality, search completeness or native execution correctness. -/
theorem decoded_render_checked_text {input : String} {decoded : FOFFrontend.Decoded}
    (decodedOk : FOFFrontend.decode input = .ok decoded)
    {certificate : Certificate} {exported : Export}
    (built : build decoded certificate = .ok exported)
    {label text : String} (printed : render label exported = .ok text) :
    ∃ original seen events parsed,
      FOFGrammar.Parses (Source.Grammar.spelling input) original ∧
      TraceEvents exported exported.trace.rows [] seen events ∧
      Source.RelatedLists (EventMeaning exported.trace.signature label) events parsed ∧
      SourcesBefore [] events ∧
      (∀ event ∈ events, OriginalEvent decoded event) ∧
      EventDerivation exported.trace.signature exported events ∧
      ParsedMixedRows text.toList parsed ∧
      (∀ other, ParsedMixedRows text.toList other → other = parsed) ∧
      (parsed.map parsedName).Nodup ∧
      (∃ role metadata, parsed.getLast? = some (.cnf ⟨exported.trace.finalName, role, [], metadata⟩)) ∧
      (∀ index name body row, Event.source index name body ∈ events →
        EventMeaning exported.trace.signature label (.source index name body) row →
        ∃ formula, original[index]? = some (.fof name formula) ∧
          row = .fof name formula (.function "file" [.atom label, .atom name])) := by
  obtain ⟨original, grammar, tables, names⟩ := decoded_original_tables decodedOk
  obtain ⟨seen, events, parsed, trace, meanings, sources, originals, derived, full, unique, endpoint⟩ :=
    decoded_render_parsed_endpoint decodedOk built printed
  have distinct : (parsed.map parsedName).Nodup := by
    rw [event_meaning_names meanings]
    exact rendered_event_names_nodup decodedOk built trace
  refine ⟨original, seen, events, parsed, grammar, trace, meanings, sources, originals,
    derived, full, unique, distinct, endpoint, ?_⟩
  intro index name body row member meaning
  exact source_event_original_identity tables names built (originals _ member) meaning

end Fang.FofTstpExport.RenderProof
