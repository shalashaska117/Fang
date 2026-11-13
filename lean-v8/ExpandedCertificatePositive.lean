/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel-evaluated nonvacuity controls for the first replay stage: the original
   byte decoder and readInput succeed on concrete inputs, including retained
   zero-output rows. Transport and the extracted preprocessing calls are not
   evaluated here; their modules alone load close to the 4-GiB proof guard. -/
import ExpandedSource

namespace Fang.TptpCandidate.FullFof.Integration.V8Positive
open Fang.TptpCandidate.FullFof.Integration

def falseInput : List UInt8 := "cnf(a,axiom,($false)).".toUTF8.data.toList

def rowsInput : List UInt8 :=
  "cnf(z,axiom,$true).cnf(a,axiom,p).cnf(y,axiom,~$false).fof(b,axiom,~p).cnf(w,axiom,$true).".toUTF8.data.toList

def shape (bytes : List UInt8) : Option (Nat × Nat × Nat) :=
  ((CnfBoolean.decodeBytes bytes 1048576).toOption.bind readInput).map fun input =>
    (input.rows.length, input.declarations.length, input.predicates.length)

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000

/-- One row, one empty clause, no predicate. -/
theorem false_clause_reads : shape falseInput = some (1, 1, 0) := by cbv

/-- Five rows are retained; the two true rows and the double negation of false
    contribute no declaration; one predicate is collected. -/
theorem omitted_rows_read : shape rowsInput = some (5, 2, 1) := by cbv

#print axioms Fang.TptpCandidate.FullFof.Integration.V8Positive.false_clause_reads
#print axioms Fang.TptpCandidate.FullFof.Integration.V8Positive.omitted_rows_read

end Fang.TptpCandidate.FullFof.Integration.V8Positive
