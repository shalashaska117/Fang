/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed byte controls for the coverage framer. -/
import BundleFramer

namespace Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls

open Fang.TptpCandidate.FullFof.Coverage
open Fang.TptpCandidate.FullFof.Coverage.FramerV2

/-- One character per byte, as the lexer reads them. -/
def bytesOf (text : String) : List UInt8 := text.toList.map (fun c => c.toNat.toUInt8)

def frame (text : String) : Except Error (List Statement) := frameFile (bytesOf text) 4096

def kindOf : Except Error (List Statement) → Option ErrorKind
  | .error failure => some failure.kind
  | .ok _ => none

def records : Except Error (List Statement) → List Declaration
  | .ok statements => statements.filterMap fun
    | .formula value => some value
    | .directive _ _ => none
  | .error _ => []

def predicatesOf (result : Except Error (List Statement)) : List (String × Nat) :=
  (source (records result)).flatMap Formula.predicates

def functionsOf (result : Except Error (List Statement)) : List (String × Nat) :=
  (source (records result)).flatMap Formula.functions

def objectsOf (result : Except Error (List Statement)) : Nat := (objectNames (records result)).length

theorem include_with_names :
    frame "include('Axioms/a.ax',[x,'y',3])." =
      .ok [.directive ["Axioms", "a.ax"] (.names [.atom "x", .atom "y", .integer "3"])] := by cbv

theorem include_with_star : frame "include(a,*)." = .ok [.directive ["a"] .star] := by cbv

/-- Decided OPEN-2: an escaping path frames to the part list no key matches. -/
theorem escaping_paths_resolve_nowhere :
    frame "include('/etc/x'). include('../x'). include('a//b')." =
      .ok [.directive [""] .absent, .directive [""] .absent, .directive [""] .absent] := by cbv

theorem include_namespace_unsupported : kindOf (frame "include(a,[x],space).") = some .unsupported := by cbv

theorem include_empty_selection_invalid : kindOf (frame "include(a,[]).") = some .invalid := by cbv

theorem annotation_does_not_change_meaning :
    predicatesOf (frame "fof(a,axiom,p(b),file('x.p',a),[status(thm),f(\"o\",1.5,X)]).") =
      predicatesOf (frame "fof(a,axiom,p(b)).") ∧
    functionsOf (frame "fof(a,axiom,p(b),file('x.p',a),[status(thm),f(\"o\",1.5,X)]).") =
      functionsOf (frame "fof(a,axiom,p(b)).") := by cbv

theorem annotation_objects_not_in_inventory :
    objectsOf (frame "fof(a,axiom,p,inference(r,[],[\"x\",\"y\"])).") = 0 := by cbv

theorem malformed_annotations_invalid :
    kindOf (frame "fof(a,axiom,p,).") = some .invalid ∧
    kindOf (frame "fof(a,axiom,p,a,b).") = some .invalid ∧
    kindOf (frame "fof(a,axiom,p,a,[],c).") = some .invalid ∧
    kindOf (frame "fof(a,axiom,p,$fof(p]).") = some .invalid := by cbv

theorem objects_inventory :
    objectsOf (frame "fof(a,axiom,\"x\" != \"y\" & q(\"x\")). cnf(b,axiom,\"z\" = c).") = 3 := by cbv

theorem object_spellings_are_distinct_from_atoms :
    functionsOf (frame "fof(a,axiom,p(\"cat\") & p('cat') & p(cat)).") =
      [(objectName "cat", 0), ("cat", 0), ("cat", 0)] := by cbv

theorem objects_are_constants_only :
    kindOf (frame "fof(a,axiom,\"a\").") = some .invalid ∧
    kindOf (frame "fof(a,axiom,p(\"a\"(b))).") = some .invalid ∧
    kindOf (frame "fof(\"a\",axiom,p).") = some .invalid ∧
    kindOf (frame "fof(a,axiom,p(\"\")).") = some .invalid ∧
    kindOf (frame "fof(a,axiom,p(\"open)).") = some .invalid := by cbv

/-- Decided OPEN-8, OPEN-9, OPEN-10 and the remaining typed rejections. -/
theorem profile_rejections :
    kindOf (frame "fof(a,axiom,p(1.5)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,1 = 2).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,$less(a,b)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,$distinct(a,b)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,$$f(a)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p(`X)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,[p] --> [q]).") = some .unsupported ∧
    kindOf (frame "tpi(a,axiom,p).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,$fof(p)).") = some .invalid ∧
    kindOf (frame "fof(1.5,axiom,p).") = some .invalid := by cbv

/-- Revision 2: the profile rejections that `profile_rejections` left to the
    agreement corpus. Numbers of every form, `$ite`, type names, undefined
    `$words`, arithmetic, and statements of the typed languages. -/
theorem profile_rejections_typed :
    kindOf (frame "fof(a,axiom,p(1/2)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p(-1/2)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p(-7)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p(1.5e-3)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,$ite(p,q,r)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p($ite(p,a,b))).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p($i)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p($o)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p($int)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p($tType)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,$foo(a)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p($foo)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p($)).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,$sum(a,b) = c).") = some .unsupported ∧
    kindOf (frame "cnf(a,axiom,p($to_real(a))).") = some .unsupported ∧
    kindOf (frame "cnf(a,axiom,$distinct(a,b)).") = some .unsupported ∧
    kindOf (frame "tff(a,axiom,p).") = some .unsupported ∧
    kindOf (frame "thf(a,axiom,p).") = some .unsupported ∧
    kindOf (frame "tcf(a,axiom,p).") = some .unsupported ∧
    kindOf (frame "fof(a,axiom,p). tff(b,type,q: $o).") = some .unsupported := by cbv

/-- Revision 2: a record cut off after its annotation comma is invalid input
    (the frozen framer reported unsupported here). -/
theorem truncated_annotation_invalid :
    kindOf (frame "cnf(c,axiom,p | q(X),inferenc") = some .invalid ∧
    kindOf (frame "fof(a,axiom,p,file(f)") = some .invalid ∧
    kindOf (frame "fof(a,axiom,p,file(f).") = some .invalid := by cbv

theorem duplicate_name_in_one_file_invalid :
    kindOf (frame "fof(x,axiom,q). fof(x,axiom,~q).") = some .invalid := by cbv

def top : Key := ⟨.base, ["input"]⟩
def axiomsKey : Key := ⟨.base, ["ax.ax"]⟩

def framedOk (files : List (Key × String)) : Bundle :=
  match frameBundle (files.map fun pair => (pair.1, bytesOf pair.2)) 4096 with
  | .ok bundle => bundle
  | .error _ => []

theorem shape_accepts_reached_files :
    wellShaped (framedOk [(top, "include('ax.ax')."), (axiomsKey, "fof(x,axiom,p).")]) 17 = true := by cbv

theorem shape_rejects_unreached_file :
    wellShaped (framedOk [(top, "fof(x,axiom,p)."), (axiomsKey, "fof(y,axiom,p).")]) 17 = false := by cbv

theorem shape_rejects_misordered_files :
    wellShaped (framedOk [(top, "include('a.ax'). include('ax.ax')."), (axiomsKey, "fof(x,axiom,p)."),
      (⟨.base, ["a.ax"]⟩, "fof(y,axiom,p).")]) 17 = false := by cbv

theorem shape_rejects_duplicate_keys :
    wellShaped (framedOk [(top, "include('ax.ax')."), (axiomsKey, "fof(x,axiom,p)."),
      (axiomsKey, "fof(y,axiom,p).")]) 17 = false := by cbv

#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.include_with_names
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.include_with_star
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.escaping_paths_resolve_nowhere
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.include_namespace_unsupported
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.include_empty_selection_invalid
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.annotation_does_not_change_meaning
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.annotation_objects_not_in_inventory
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.malformed_annotations_invalid
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.objects_inventory
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.object_spellings_are_distinct_from_atoms
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.objects_are_constants_only
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.profile_rejections
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.profile_rejections_typed
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.truncated_annotation_invalid
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.duplicate_name_in_one_file_invalid
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.shape_accepts_reached_files
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.shape_rejects_unreached_file
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.shape_rejects_misordered_files
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls.shape_rejects_duplicate_keys

end Fang.TptpCandidate.FullFof.Coverage.FramerV2.Controls
