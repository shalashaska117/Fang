/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed byte controls for the bundle numeric input. -/
import BundleNumeric

namespace Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls

open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2
open Fang.TptpCandidate.FullFof.Coverage.BundleV8

def bytesOf (text : String) : List UInt8 := text.toList.map (fun c => c.toNat.toUInt8)

def top : Key := ⟨.base, ["top.p"]⟩
def axioms : Key := ⟨.base, ["a.ax"]⟩

def run (files : List (Key × String)) : Except BundleError Integration.NumericInput :=
  bundleNumeric (files.map fun pair => (pair.1, bytesOf pair.2)) 4096

/-- Outcome summary: declaration count, row count and table sizes, or a label. -/
def summary : Except BundleError Integration.NumericInput → String
  | .ok input => s!"ok {input.declarations.length} {input.rows.length} {input.functions.length} {input.predicates.length}"
  | .error (.frame _) => "frame"
  | .error .shape => "shape"
  | .error (.expand .missing) => "missing"
  | .error (.expand .cycle) => "cycle"
  | .error (.expand .selectionMissing) => "selection-missing"
  | .error (.expand .selectionAmbiguous) => "selection-ambiguous"
  | .error (.expand .fuel) => "fuel"
  | .error .nonliteral => "nonliteral"

/-- Two objects give one generated clause in one extra row after the two
    original rows; the include is replaced in place. -/
theorem objects_add_one_row :
    summary (run [(top, "include('a.ax'). fof(x,axiom,p(\"u\") & p(\"v\")).") ,
      (axioms, "fof(y,axiom,q).")]) = "ok 3 3 2 2" := by cbv

/-- Without objects the input is the accepted `readInput` result unchanged. -/
theorem no_objects_no_row :
    summary (run [(top, "include('a.ax',[y]). cnf(x,axiom,p(a) | ~q)."),
      (axioms, "fof(y,axiom,q). fof(z,axiom,r).")]) = "ok 2 2 1 2" := by cbv

theorem three_objects_three_clauses :
    summary (run [(top, "fof(x,axiom,p(\"a\") & p(\"b\") & p(\"c\"),file(f,x)).")]) = "ok 4 2 3 1" := by cbv

theorem missing_file : summary (run [(top, "include('nope.ax').")]) = "missing" := by cbv

theorem unreached_file_is_shape :
    summary (run [(top, "fof(x,axiom,p)."), (axioms, "fof(y,axiom,q).")]) = "shape" := by cbv

theorem self_include_is_cycle : summary (run [(top, "include('top.p').")]) = "cycle" := by cbv

theorem selection_missing :
    summary (run [(top, "include('a.ax',[nope])."), (axioms, "fof(y,axiom,q).")]) = "selection-missing" := by cbv

theorem framing_error : summary (run [(top, "fof(x,axiom,p(1.5)).")]) = "frame" := by cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls.objects_add_one_row
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls.no_objects_no_row
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls.three_objects_three_clauses
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls.missing_file
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls.unreached_file_is_shape
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls.self_include_is_cycle
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls.selection_missing
#print axioms Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls.framing_error

end Fang.TptpCandidate.FullFof.Coverage.BundleV8.Controls
