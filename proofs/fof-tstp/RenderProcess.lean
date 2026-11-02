/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.MixedRows

namespace Fang.FofTstpExport.RenderProof

abbrev State := List Nat × List String

/-- Expose the actual mutable loop body for induction. `render_eq_run` checks
    the connection by definitional equality, not by a separate model test. -/
def process (fileLabel : String) (exported : Export) (row : TstpExport.Row)
    (state : State) : Except String (ForInStep State) := do
  let problem := exported.trace.signature
  let mut emittedFormulas := state.1
  let mut lines := state.2
  match row.origin with
  | .input sourceIndex _ =>
    let some leaf := exported.leaves[sourceIndex]?
      | throw "export-error: missing original leaf ancestry"
    if row.name != leaf.rawName || !decide (row.clause = leaf.clause) then
      throw "export-error: trace leaf differs from original ancestry"
    match leaf.body with
    | .cnf _ =>
      lines := lines ++ [← TstpExport.renderRow problem fileLabel row]
    | .fof body =>
      if !emittedFormulas.contains leaf.declaration then
        lines := lines ++ [← sourceFormula problem fileLabel leaf.sourceName body]
        emittedFormulas := leaf.declaration :: emittedFormulas
      lines := lines ++ [← clausifiedRow problem leaf]
  | _ => lines := lines ++ [← TstpExport.renderRow problem fileLabel row]
  pure (.yield (emittedFormulas, lines))

def run (fileLabel : String) (exported : Export) : Except String State :=
  forIn exported.trace.rows ([], []) (process fileLabel exported)

theorem render_eq_run (fileLabel : String) (exported : Export) :
    render fileLabel exported = (do
      discard (TstpExport.quote fileLabel)
      let state ← run fileLabel exported
      let text := String.join state.2
      if text.utf8ByteSize > 16 * 1024 * 1024 then
        throw "resource-exhaustion: TSTP output exceeds 16 MiB"
      pure text) := by
  rfl

end Fang.FofTstpExport.RenderProof
