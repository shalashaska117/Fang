/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Shared data for the finite model export kernel controls. -/
import ModelExport
import NativeLimits

namespace Fang.TptpCandidate.FullFof.Model.ExportControls
open Fang.TptpCandidate.FullFof.Model


/-- One byte per character, as the decoders read ASCII input. -/
def bytesOf (text : String) : List UInt8 := text.toList.map fun character => character.toNat.toUInt8

def top : Coverage.Key := ⟨.base, ["input"]⟩

def single (layout : Layout) (input certificate : String) : Except ExportFailure String :=
  exportSingle defaultLimits layout Fang.NativeLimits.declarationLimit (bytesOf input) 4096 certificate

def bundle (input certificate : String) : Except ExportFailure String :=
  exportBundle defaultLimits defaultLayout [(top, bytesOf input)] 4096 certificate

def inputs (input certificate : String) : Except ExportFailure String :=
  exportInputs defaultLimits defaultLayout [(top, bytesOf input)] 4096 certificate

def goal (input certificate : String) (index : Nat) : Except ExportFailure String :=
  exportGoal defaultLimits defaultLayout [(top, bytesOf input)] 4096 index certificate

/-- The document, compared as a Boolean so that the kernel decides it. -/
def prints {α : Type} (outcome : Except α String) (expected : String) : Bool :=
  match outcome with
  | .ok text => text == expected
  | .error _ => false

def documentFailure (outcome : Except ExportFailure String) : Option String :=
  match outcome with
  | .error (.document message) => some message
  | _ => none

def checkFailure (outcome : Except ExportFailure String) : Bool :=
  match outcome with
  | .error (.check _) => true
  | _ => false

/-- At most one cell is written in full. -/
def oneCellLayout : Layout := { defaultLayout with cells := 1 }

/-- `p(c)` with `c` = 0 and `p` true at 0. Names are hexadecimal: `c` is 63, `p` is 70. -/
def unitInput : String := "fof(a,axiom,p(c))."
def unitModel : String := "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 1\nend\n"
def unitDocument : String :=
  "fof(fang_domain,fi_domain,\n    ! [X] : X = \"e0\" ).\n" ++
  "fof(fang_function_1,fi_functors,\n    c = \"e0\" ).\n" ++
  "fof(fang_predicate_1,fi_predicates,\n    p(\"e0\") ).\n"
end Fang.TptpCandidate.FullFof.Model.ExportControls
