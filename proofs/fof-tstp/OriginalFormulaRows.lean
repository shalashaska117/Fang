/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Draft: not accepted until the next full proof gate. -/
import Fang.FOF.TSTP.NamePartition
import Fang.FOF.TSTP.SourceIdentity

namespace Fang.FofTstpExport.RenderProof
open FofTstpText TstpText

/-- Retain one original grammar witness together with the exact decoder tables
    and declaration-name order. This uses the existing parser result theorem. -/
theorem decoded_original_tables {input : String} {decoded : FOFFrontend.Decoded}
    (success : FOFFrontend.decode input = .ok decoded) :
    ∃ named, FOFGrammar.Parses (Source.Grammar.spelling input) named ∧
      Source.RelatedLists (FOFFrontend.TableDeclarationEncoding decoded.state) named decoded.declarations ∧
      decoded.state.clauseNames = named.map NamedFOF.Declaration.name := by
  cases tokenized : FOFFrontend.tokenize input with
  | error reason => simp [FOFFrontend.decode, tokenized, bind, Except.bind] at success
  | ok tokens =>
    cases parsed : FOFFrontend.statements (tokens.length + 1)
        { tokens, endOffset := input.utf8ByteSize } with
    | error reason => simp [FOFFrontend.decode, tokenized, parsed, bind, Except.bind] at success
    | ok pair =>
      rcases pair with ⟨declarations, state⟩
      simp only [FOFFrontend.decode, tokenized, parsed, bind, Except.bind, pure, Except.pure] at success
      cases success
      obtain ⟨named, encoding, _, names, unique, grammar⟩ :=
        FOFFrontend.raw_statements_grammar (tokens.length + 1) (by simp) parsed
      exact ⟨named,
        ⟨tokens, (FOFFrontend.fof_tokenize_bytes_iff input tokens).mp tokenized,
          grammar, by simpa using unique⟩,
        encoding, by simpa using names⟩

theorem related_index_right {relation : α → β → Prop} {left : List α} {right : List β}
    (related : Source.RelatedLists relation left right) {index : Nat} {value : β}
    (found : right[index]? = some value) :
    ∃ original, left[index]? = some original ∧ relation original value := by
  induction related generalizing index with
  | nil => simp at found
  | @cons original numeric originals numerics head tail ih =>
    cases index with
    | zero =>
      have same : numeric = value := Option.some.inj found
      exact ⟨original, rfl, same ▸ head⟩
    | succ index =>
      obtain ⟨original, atOriginal, relation⟩ := ih (by simpa using found)
      exact ⟨original, by simpa using atOriginal, relation⟩

/-- A parsed inserted FOF axiom contains the exact original named formula at
    its declared source position, not merely an equisatisfiable replacement. -/
theorem source_event_original_identity {decoded : FOFFrontend.Decoded} {named : List NamedFOF.Declaration}
    (tables : Source.RelatedLists (FOFFrontend.TableDeclarationEncoding decoded.state) named decoded.declarations)
    (names : decoded.state.clauseNames = named.map NamedFOF.Declaration.name)
    {certificate : Certificate} {exported : Export} (built : build decoded certificate = .ok exported)
    {index name body label parsed}
    (original : OriginalEvent decoded (.source index name body))
    (meaning : EventMeaning exported.trace.signature label (.source index name body) parsed) :
    ∃ formula, named[index]? = some (.fof name formula) ∧
      parsed = .fof name formula (.function "file" [.atom label, .atom name]) := by
  obtain ⟨declaration, atSource, encoding⟩ := related_index_right tables original.1
  cases meaning with
  | source printed =>
    cases encoding with
    | fof variables actualName ground relation =>
      rename_i formula
      have sourceNameAt : decoded.state.clauseNames[index]? = some actualName := by
        rw [names]
        simp [List.getElem?_map, atSource, NamedFOF.Declaration.name]
      have nameEq : actualName = name := Option.some.inj (sourceNameAt.symm.trans original.2)
      have formulaEq := ground_formula_identity
        (state := { decoded.state with variables })
        (problem := exported.trace.signature)
        (by rw [(build_trace_endpoint built).1]; rfl)
        (by rw [(build_trace_endpoint built).1]; rfl)
        relation ground printed
      refine ⟨formula, ?_, ?_⟩
      · simpa only [nameEq] using atSource
      · simp only [formulaEq]

end Fang.FofTstpExport.RenderProof
