/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel controls for the hashed bundle framer: the controls of `BundleFramerLimitControls` with the same expected outcomes, evaluated on the hashed framer, the last two at `Fang.NativeLimits.declarationLimit`. -/
import BundleFramerHashed
import NativeLimits

namespace Fang.TptpCandidate.FullFof.Coverage.FramerLimit.HashedControls

open Fang.TptpCandidate.FullFof.Coverage

/-- One character per byte, as the framer lexer reads them. -/
private def bytesOf (text : String) : List UInt8 := text.toList.map (fun c => c.toNat.toUInt8)

private def top : Key := ⟨.base, ["input"]⟩
private def axiomsKey : Key := ⟨.base, ["ax.ax"]⟩

private def sealed (files : List (Key × String)) : List (Key × List UInt8) :=
  files.map fun pair => (pair.1, bytesOf pair.2)

/-- The test holds for the hashed framer at this limit. -/
private def both (limit : Nat) (files : List (Key × String)) (test : Except Error Bundle → Bool) : Bool :=
  test (frameBundleHashed limit (sealed files) 4096)

/-- The statement count of every file, or nothing on a refusal. -/
private def counts : Except Error Bundle → Option (List Nat)
  | .ok bundle => some (bundle.map fun file => file.statements.length)
  | .error _ => none

/-- The refusal kind and offset, or nothing on success. -/
private def refusal : Except Error Bundle → Option (ErrorKind × Nat)
  | .ok _ => none
  | .error problem => some (problem.kind, problem.offset)

private def twoFormulas : String := "fof(a,axiom,p).fof(b,axiom,q)."

/-- A second formula over a limit of one is refused as a resource at its first byte. -/
theorem hashed_over_limit_refused : both 1 [(top, twoFormulas)] (fun result => refusal result == some (.resource, 15)) := by
  cbv

/-- Two formulas at a limit of two are framed. -/
theorem hashed_at_limit_accepted : both 2 [(top, twoFormulas)] (fun result => counts result == some [2]) := by
  cbv

/-- The limit counts formulas per file, and an include directive is not counted. -/
theorem hashed_limit_per_file :
    both 1 [(top, "include('ax.ax').fof(a,axiom,p)."), (axiomsKey, "fof(b,axiom,q).")]
      (fun result => counts result == some [2, 1]) := by
  cbv

/-- A statement after the last allowed formula is refused even when it is an include directive. -/
theorem hashed_include_after_limit_refused :
    both 1 [(top, "fof(a,axiom,p).include('ax.ax')."), (axiomsKey, "fof(b,axiom,q).")]
      (fun result => refusal result == some (.resource, 15)) := by
  cbv

/-- A repeated name is still refused as invalid at the decision-9 limit. -/
theorem hashed_duplicate_refused :
    both Fang.NativeLimits.declarationLimit [(top, "fof(a,axiom,p).fof(a,axiom,q).")]
      (fun result => (refusal result).map Prod.fst == some .invalid) := by
  cbv

/-- The same name in two files is not a repeat: names are checked per file. -/
theorem hashed_same_name_other_file_accepted :
    both Fang.NativeLimits.declarationLimit
      [(top, "include('ax.ax').fof(a,axiom,p)."), (axiomsKey, "fof(a,axiom,q).")]
      (fun result => counts result == some [2, 1]) := by
  cbv

/-- The decision-9 limit is the literal limit of the list-framer controls. -/
theorem declarationLimit_value : Fang.NativeLimits.declarationLimit = 65536 := rfl

#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.HashedControls.declarationLimit_value
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.HashedControls.hashed_over_limit_refused
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.HashedControls.hashed_at_limit_accepted
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.HashedControls.hashed_limit_per_file
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.HashedControls.hashed_include_after_limit_refused
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.HashedControls.hashed_duplicate_refused
#print axioms Fang.TptpCandidate.FullFof.Coverage.FramerLimit.HashedControls.hashed_same_name_other_file_accepted

end Fang.TptpCandidate.FullFof.Coverage.FramerLimit.HashedControls
