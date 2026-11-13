/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TSTP.RenderProcess

namespace Fang.FofTstpExport.GuardControls

private def fixture (items : List Leaf) : Export := {
  decoded := { declarations := [], state := { tokens := [], endOffset := 0 } }
  leaves := items
  trace := {
    signature := {
      signature := { problem := [], functionArities := [], predicateArities := [] }
      functions := []
      predicates := []
      names := []
    }
    rows := []
    finalName := "source"
  }
}

private def leaf (clause : Clause) : Leaf := {
  declaration := 0
  localClause := 0
  sourceName := "source"
  rawName := "source"
  body := .cnf clause
  clause
}

private def row (name : String) (clause : Clause) : TstpExport.Row := {
  name, clause, origin := .input 0 "source"
}

private def literal (constant : Nat) : Literal := {
  positive := true, atom := { pred := 0, args := [.app 0 [.app constant []]] }
}

theorem missing_leaf_rejected :
    RenderProof.process "problem.p" (fixture []) (row "source" []) ([], []) =
      .error "export-error: missing original leaf ancestry" := by rfl

theorem changed_name_rejected :
    RenderProof.process "problem.p" (fixture [leaf []]) (row "changed" []) ([], []) =
      .error "export-error: trace leaf differs from original ancestry" := by rfl

theorem changed_nested_term_rejected :
    RenderProof.process "problem.p" (fixture [leaf [literal 1]])
      (row "source" [literal 2]) ([], []) =
      .error "export-error: trace leaf differs from original ancestry" := by
  have different : [literal 2] ≠ [literal 1] := by decide +kernel
  simp [RenderProof.process, fixture, leaf, row, different, throw, throwThe, bind, Except.bind]
  rfl

theorem matching_empty_clause_printed :
    RenderProof.process "problem.p" (fixture [leaf []]) (row "source" []) ([], []) =
      .ok (.yield ([], ["cnf('source',axiom,($false),file('problem.p','source')).\n"])) := by rfl

end Fang.FofTstpExport.GuardControls
