/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   One limits record for every native main, so that the checkers cannot drift
   apart. Declarations, the whole-problem Skolem work
   counters and the three symbol caps are set here; every
   per-formula, per-block and per-clause limit is the earlier one.

   Each symbol cap is the largest count of its worst shape that finished inside
   the native guard of 60 s and 2 GiB in any measurement round, plus 10 percent,
   rounded up. Counts in that margin end in the guard's ResourceOut, which is
   sound, and no count that finished in a measurement is refused:
   - `max_functions` 7081: 6437 distinct constants finished in 58.1 s
     in the first measurement round.
   - `maximumPredicates` 5808: 5279 distinct predicates finished in 57.3 s on the
     earlier checker; 5807
     predicates plus the reserved equality slot.
   - `max_skolem_symbols` 4703: 4275 existentials, one per declaration, finished
     in 59.7 s in the second measurement round. Skolemization checks
     this cap only when it creates symbol 4704, so inputs at the cap and one
     above it can both end in the guard. -/
import OriginalReplay

open Aeneas.Std

namespace Fang.NativeLimits

/-- Input bytes read from one file. -/
def byteLimit : Nat := 1024 * 1024

/-- Declarations in one input, for the decoder and for Skolemization. -/
def declarationLimit : Nat := 65536

/-- Predicates in the transport table, counting the reserved equality slot. -/
def maximumPredicates : Usize := 5808#usize

/-- Literals in one clause, at equality conversion. -/
def maximumLiterals : Usize := 256#usize

/-- Skolemization credits cover the whole FOF list; removal and clausification
    credits apply per block. -/
def replayLimits : FangOriginalReplay.Limits := {
  skolem := {
    core := {
      max_formula_depth := 64#usize, max_formula_nodes := 10000#usize,
      max_term_depth := 64#usize, max_input_term_nodes := 100000#usize,
      max_clauses := 1000#usize, max_literals_per_clause := 256#usize,
      max_literals := 100000#usize, max_stored_nodes := 4000000#usize,
      max_operations := 16000000#usize, max_binders := 10000#usize }
    max_declarations := 65536#usize, max_functions := 7081#usize,
    max_skolem_symbols := 4703#usize }
  removal := {
    max_formula_depth := 64#usize, max_operations := 5000000#usize,
    max_output_nodes := 1000000#usize }
  clausification := {
    max_formula_depth := 64#usize, max_formula_nodes := 10000#usize,
    max_term_depth := 64#usize, max_input_term_nodes := 100000#usize,
    max_clauses := 1000#usize, max_literals_per_clause := 256#usize,
    max_literals := 100000#usize, max_stored_nodes := 1000000#usize,
    max_operations := 5000000#usize } }

/-- The Skolem declaration limit is the decoder's. -/
theorem skolem_declarations : replayLimits.skolem.max_declarations.val = declarationLimit := rfl

#print axioms Fang.NativeLimits.skolem_declarations

end Fang.NativeLimits
