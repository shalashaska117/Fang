/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.RenderEvents

namespace Fang.FofTstpExport.RenderProof

def SourceParent (history : List Event) (leaf : Leaf) : Prop :=
  ∃ body, leaf.body = .fof body ∧
    Event.source leaf.declaration leaf.sourceName body ∈ history

/-- Each clausification names an original formula printed earlier. -/
def SourcesBefore (history : List Event) : List Event → Prop
  | [] => True
  | event :: rest =>
    (match event with | .clausify leaf => SourceParent history leaf | _ => True) ∧
      SourcesBefore (history ++ [event]) rest

def SourcesReady (exported : Export) (seen : List Nat) (history : List Event) : Prop :=
  ∀ leaf ∈ exported.leaves, leaf.declaration ∈ seen → ∀ body, leaf.body = .fof body →
    Event.source leaf.declaration leaf.sourceName body ∈ history

theorem leaf_source_unique {decoded : FOFFrontend.Decoded} {certificate : Certificate}
    {exported : Export} (built : build decoded certificate = .ok exported)
    {first second : Leaf} (firstIn : first ∈ exported.leaves) (secondIn : second ∈ exported.leaves)
    (same : first.declaration = second.declaration) :
    first.sourceName = second.sourceName ∧ first.body = second.body := by
  obtain ⟨firstBody, firstName, _⟩ := leaves_origin (build_source built).2 firstIn
  obtain ⟨secondBody, secondName, _⟩ := leaves_origin (build_source built).2 secondIn
  rw [same] at firstBody firstName
  exact ⟨Option.some.inj (firstName.symm.trans secondName),
    Option.some.inj (firstBody.symm.trans secondBody)⟩

private theorem input_leaf_member {exported row leaf} (input : InputLeaf exported row leaf) :
    leaf ∈ exported.leaves := by
  obtain ⟨index, _, _, found, _, _⟩ := input
  exact List.mem_of_getElem? found

theorem SourcesReady.append {exported seen history} (ready : SourcesReady exported seen history)
    (more : List Event) : SourcesReady exported seen (history ++ more) := by
  intro leaf member seen body shape
  exact List.mem_append_left more (ready leaf member seen body shape)

private theorem SourcesReady.fresh {decoded : FOFFrontend.Decoded} {certificate : Certificate}
    {exported : Export} (built : build decoded certificate = .ok exported)
    {seen history leaf body} (ready : SourcesReady exported seen history)
    (member : leaf ∈ exported.leaves) (shape : leaf.body = .fof body) :
    SourcesReady exported (leaf.declaration :: seen)
      (history ++ [.source leaf.declaration leaf.sourceName body, .clausify leaf]) := by
  intro other otherIn seenOther otherBody otherShape
  rcases List.mem_cons.mp seenOther with same | earlier
  · obtain ⟨sameName, sameBody⟩ := leaf_source_unique built otherIn member same
    have sameFormula : otherBody = body :=
      GroundFOF.Declaration.fof.inj (otherShape.symm.trans (sameBody.trans shape))
    simp only [same, sameName, sameFormula]
    exact List.mem_append_right _ (by simp)
  · exact List.mem_append_left _ (ready other otherIn earlier otherBody otherShape)

theorem row_events_sources {decoded : FOFFrontend.Decoded} {certificate : Certificate}
    {exported : Export} (built : build decoded certificate = .ok exported)
    {row before after events history}
    (step : RowEvents exported row before after events)
    (ready : SourcesReady exported before history) :
    SourcesBefore history events ∧ SourcesReady exported after (history ++ events) := by
  cases step with
  | derived notInput => exact ⟨⟨True.intro, True.intro⟩, ready.append _⟩
  | cnf input body => exact ⟨⟨True.intro, True.intro⟩, ready.append _⟩
  | @seen leaf body input shape seen =>
    have prior := ready leaf (input_leaf_member input) seen body shape
    exact ⟨⟨⟨body, shape, prior⟩, True.intro⟩, ready.append _⟩
  | @fresh leaf body input shape absent =>
    refine ⟨⟨True.intro, ⟨⟨body, shape, ?_⟩, True.intro⟩⟩,
      ready.fresh built (input_leaf_member input) shape⟩
    exact List.mem_append_right _ (by simp)

theorem SourcesBefore.append {history first rest}
    (head : SourcesBefore history first) (tail : SourcesBefore (history ++ first) rest) :
    SourcesBefore history (first ++ rest) := by
  induction first generalizing history with
  | nil => simpa using tail
  | cons event events ih =>
    exact ⟨head.1, ih head.2 (by simpa [List.append_assoc] using tail)⟩

theorem trace_events_sources {decoded : FOFFrontend.Decoded} {certificate : Certificate}
    {exported : Export} (built : build decoded certificate = .ok exported)
    {rows before after events history}
    (trace : TraceEvents exported rows before after events)
    (ready : SourcesReady exported before history) :
    SourcesBefore history events ∧ SourcesReady exported after (history ++ events) := by
  induction trace generalizing history with
  | nil => exact ⟨True.intro, by simpa using ready⟩
  | cons head tail ih =>
    obtain ⟨sources, next⟩ := row_events_sources built head ready
    obtain ⟨later, final⟩ := ih next
    exact ⟨sources.append later, by simpa [List.append_assoc] using final⟩

theorem built_render_sources {decoded : FOFFrontend.Decoded} {certificate : Certificate}
    {exported : Export} (built : build decoded certificate = .ok exported)
    {label text : String} (printed : render label exported = .ok text) :
    ∃ seen events texts, text = String.join texts ∧
      TraceEvents exported exported.trace.rows [] seen events ∧
      Source.RelatedLists (EventText exported.trace.signature label) events texts ∧
      SourcesBefore [] events := by
  obtain ⟨seen, events, texts, same, trace, meanings⟩ := render_events label exported printed
  have ready : SourcesReady exported [] [] := by intro leaf member impossible; cases impossible
  exact ⟨seen, events, texts, same, trace, meanings, (trace_events_sources built trace ready).1⟩

end Fang.FofTstpExport.RenderProof
