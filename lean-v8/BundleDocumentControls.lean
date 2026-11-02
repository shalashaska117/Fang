/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Fixed controls for bundle source rows, with the helpers the two row
   controls share. The row controls each have a module of their own
   (`BundleDocumentObjectRows`, `BundleDocumentFileRows`) to keep every
   compile well under the memory guard. Here: two files that print the same
   path make export fail, and object entries are renamed. -/
import BundleSourceRow

namespace Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls

open Fang.TptpCandidate.FullFof
open Fang.TptpCandidate.FullFof.Coverage (Key Item Bundle expand)
open Fang.QuantifiedEqualityTstp.Expanded.Bundle

def bytesOf (text : String) : List UInt8 := text.toList.map (fun c => c.toNat.toUInt8)

def top : Key := ⟨.base, ["top.p"]⟩

def framed (files : List (Key × String)) : Bundle :=
  match Coverage.FramerV2.frameBundle (files.map fun pair => (pair.1, bytesOf pair.2)) 4096 with
  | .ok bundle => bundle
  | .error _ => []

def itemsOf (bundle : Bundle) : List Item :=
  match expand bundle 17 with
  | .ok items => items
  | .error _ => []

def rowsOf (files : List (Key × String)) : Except String (List (String × String)) :=
  bundleSourceRows (framed files) (itemsOf (framed files))

def texts : Except String (List (String × String)) → List String
  | .ok rows => rows.map Prod.snd
  | .error reason => [reason]

/-- A base file and a TPTP-root file with the same path make export fail. -/
theorem same_path_fails :
    texts (rowsOf [(top, "include('a.ax'). include('Axioms/x.ax')."), (⟨.base, ["a.ax"]⟩, "fof(b1,axiom,p)."),
      (⟨.tptp, ["Axioms", "x.ax"]⟩, "include('a.ax')."), (⟨.tptp, ["a.ax"]⟩, "fof(t1,axiom,q).")]) =
      ["export-error: two bundle files print the same path"] := by
  cbv

/-- Object entries of the function table get the stem and their table index. -/
theorem objects_renamed :
    renameObjects "fang_object_" [(Coverage.FramerV2.objectName "u", 0), ("f", 1), (Coverage.FramerV2.objectName "v", 0)] =
      [("fang_object_0", 0), ("f", 1), ("fang_object_2", 0)] := by
  cbv

#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls.same_path_fails
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls.objects_renamed

end Fang.QuantifiedEqualityTstp.Expanded.Bundle.Controls
