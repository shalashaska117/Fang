/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Shared native limits, from the limit and certificate measurements of
   2026-11-04. Symbol caps include all confirmation runs.
   Depth 2,712 finished with the combined record; 2,984 is its ten-percent
   margin. A resource guard still applies below each cap. The per-block caps
   use the measured worst shape and can refuse larger blocks of faster shapes.
   The Skolem operation budget stays at 16,000,000 to preserve prior admissions.
   Input and model-certificate byte limits remain one MiB. -/
import OriginalReplay

open Aeneas.Std

namespace Fang.NativeLimits

/-- Input bytes read from one file. Also retained by the model certificate reader. -/
def byteLimit : Nat := 1024 * 1024

/-- Refutation certificate bytes, including any premise line. The narrow-chain
    measured success was 4,619,302 bytes; this adds ten percent, rounded up. -/
def certificateLimit : Nat := 5081233

/-- Declarations in one input, shared by the decoder and Skolemization. -/
def declarationLimit : Nat := 65536

/-- Shared formula height for the byte decoder and all replay stages. -/
def formulaDepthLimit : Nat := 2984

/-- Formula-size threshold used by definitional clausification. -/
def namingThreshold : Nat := 8

/-- Predicate slots, including the reserved equality slot. -/
def maximumPredicates : Usize := 74339#usize

/-- Literals in one clause at equality conversion. -/
def maximumLiterals : Usize := 256#usize

/-- Skolem credits apply to the whole task; removal and clausification credits
    apply separately to each FOF block. Unmeasured per-formula limits stay fixed. -/
def replayLimits : FangOriginalReplay.Limits := {
  skolem := {
    core := {
      max_formula_depth := 2984#usize, max_formula_nodes := 10000#usize,
      max_term_depth := 64#usize, max_input_term_nodes := 100000#usize,
      max_clauses := 1000#usize, max_literals_per_clause := 256#usize,
      max_literals := 100000#usize, max_stored_nodes := 7943814#usize,
      max_operations := 16000000#usize, max_binders := 10000#usize }
    max_declarations := 65536#usize, max_functions := 83412#usize,
    max_skolem_symbols := 30675#usize }
  removal := {
    max_formula_depth := 2984#usize, max_operations := 5000000#usize,
    max_output_nodes := 1000000#usize }
  clausification := {
    max_formula_depth := 2984#usize, max_formula_nodes := 10000#usize,
    max_term_depth := 64#usize, max_input_term_nodes := 100000#usize,
    max_clauses := 36045#usize, max_literals_per_clause := 256#usize,
    max_literals := 423500#usize, max_stored_nodes := 6657931#usize,
    max_operations := 6657983#usize } }

theorem skolem_declarations : replayLimits.skolem.max_declarations.val = declarationLimit := rfl

theorem skolem_depth : replayLimits.skolem.core.max_formula_depth.val = formulaDepthLimit := rfl

theorem removal_depth : replayLimits.removal.max_formula_depth.val = formulaDepthLimit := rfl

theorem clausification_depth : replayLimits.clausification.max_formula_depth.val = formulaDepthLimit := rfl

#print axioms Fang.NativeLimits.skolem_declarations
#print axioms Fang.NativeLimits.skolem_depth
#print axioms Fang.NativeLimits.removal_depth
#print axioms Fang.NativeLimits.clausification_depth

end Fang.NativeLimits
