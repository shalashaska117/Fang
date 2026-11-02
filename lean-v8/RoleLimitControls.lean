/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel controls for the limited framers. Each control evaluates the list framer with the gated tokenizer and the hashed framer on the same input and asks the same outcome of both. -/
import RoleFramerLimit
import NativeLimits

namespace Fang.TptpCandidate.Roles.Bundle.V3.LimitControls
open FullFof Numeric

/-- One character per byte, as the coverage lexer reads them. -/
private def bytesOf (text : String) : List UInt8 := text.toList.map (fun c => c.toNat.toUInt8)

private def top : Coverage.Key := ⟨.base, ["input"]⟩
private def axiomsKey : Coverage.Key := ⟨.base, ["ax.ax"]⟩

private def sealed (files : List (Coverage.Key × String)) : List (Coverage.Key × List UInt8) :=
  files.map fun pair => (pair.1, bytesOf pair.2)

/-- The test holds for the list framer and for the hashed framer at this limit. -/
private def both (limit : Nat) (files : List (Coverage.Key × String)) (test : Except Error RoleBundle → Bool) : Bool :=
  test (frameBundle limit V2.gated (sealed files) 4096) && test (frameBundleHashed limit (sealed files) 4096)

/-- The statement count of every file, or nothing on a refusal. -/
private def counts : Except Error RoleBundle → Option (List Nat)
  | .ok bundle => some (bundle.map fun file => file.statements.length)
  | .error _ => none

/-- The refusal kind, or nothing on success. -/
private def refusal : Except Error RoleBundle → Option ErrorKind
  | .ok _ => none
  | .error problem => some problem.kind

private def twoFormulas : String := "fof(a,axiom,p).fof(b,axiom,q)."

/-- A second formula over a limit of one is refused as a resource. -/
theorem over_limit_refused : both 1 [(top, twoFormulas)] (fun result => refusal result == some .resource) := by
  cbv

/-- Two formulas at a limit of two are framed. -/
theorem at_limit_accepted : both 2 [(top, twoFormulas)] (fun result => counts result == some [2]) := by
  cbv

/-- The limit counts formulas per file, and an include directive is not counted. -/
theorem limit_per_file :
    both 1 [(top, "include('ax.ax').fof(a,axiom,p)."), (axiomsKey, "fof(b,axiom,q).")]
      (fun result => counts result == some [2, 1]) := by
  cbv

/-- A statement after the last allowed formula is refused even when it is an include directive. -/
theorem include_after_limit_refused :
    both 1 [(top, "fof(a,axiom,p).include('ax.ax')."), (axiomsKey, "fof(b,axiom,q).")]
      (fun result => refusal result == some .resource) := by
  cbv

/-- A repeated name is still refused as invalid at the decision-9 limit. -/
theorem duplicate_refused :
    both Fang.NativeLimits.declarationLimit [(top, "fof(a,axiom,p).fof(a,axiom,q).")]
      (fun result => refusal result == some .invalid) := by
  cbv

/-- The same name in two files is not a repeat: names are checked per file. -/
theorem same_name_other_file_accepted :
    both Fang.NativeLimits.declarationLimit [(top, "include('ax.ax').fof(a,axiom,p)."), (axiomsKey, "fof(a,axiom,q).")]
      (fun result => counts result == some [2, 1]) := by
  cbv

#print axioms Fang.TptpCandidate.Roles.Bundle.V3.LimitControls.over_limit_refused
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.LimitControls.at_limit_accepted
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.LimitControls.limit_per_file
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.LimitControls.include_after_limit_refused
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.LimitControls.duplicate_refused
#print axioms Fang.TptpCandidate.Roles.Bundle.V3.LimitControls.same_name_other_file_accepted

end Fang.TptpCandidate.Roles.Bundle.V3.LimitControls
