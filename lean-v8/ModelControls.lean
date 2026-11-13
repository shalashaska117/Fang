/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Kernel controls for the model entries on small fixed inputs: accepted models on every path, and each kind of
   rejection. The accepted single-file control also yields the original-byte meaning, so the endpoint is not vacuous.
   The step controls show a model that the static estimate of `workOf` would refuse and the step-counted evaluation
   of the rewritten formula accepts. -/
import ModelEntries
import NativeLimits

namespace Fang.TptpCandidate.FullFof.Model.Controls

set_option maxRecDepth 100000
set_option cbv.maxSteps 20000000
set_option maxHeartbeats 2000000

/-- One byte per character, as the decoders read ASCII input. -/
private def bytesOf (text : String) : List UInt8 := text.toList.map fun character => character.toNat.toUInt8

private def single (input certificate : String) : Except ModelError Unit :=
  acceptsSingle defaultLimits Fang.NativeLimits.declarationLimit (bytesOf input) 4096 certificate

private def top : Coverage.Key := ⟨.base, ["input"]⟩

private def bundle (input certificate : String) : Except ModelError Unit :=
  acceptsBundle defaultLimits Coverage.BundleLimit.limited [(top, bytesOf input)] 4096 certificate

private def inputs (input certificate : String) : Except ModelError Unit :=
  acceptsInputs defaultLimits Roles.Bundle.V3.limited [(top, bytesOf input)] 4096 certificate

private def goal (input certificate : String) (index : Nat) : Except ModelError Coverage.Item :=
  acceptsGoal defaultLimits Roles.Bundle.V3.limited [(top, bytesOf input)] 4096 index certificate

private def accepted {α : Type} : Except ModelError α → Bool
  | .ok _ => true
  | .error _ => false

private def rejectedStatement {α : Type} : Except ModelError α → Option Nat
  | .error (.rejected (.statement index)) => some index
  | _ => none

private def certificateError {α : Type} : Except ModelError α → Bool
  | .error (.certificate _) => true
  | _ => false

/-- `p(c)` with `c` = 0 and `p` true at 0. Names are hexadecimal: `c` is 63, `p` is 70. -/
private def unitInput : String := "fof(a,axiom,p(c))."
private def unitModel : String := "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 1\nend\n"

theorem single_accepted : accepted (single unitInput unitModel) = true := by
  cbv

/-- The control's acceptance gives the original-byte meaning. -/
theorem single_meaning : CnfBoolean.BytesSatisfiable (bytesOf unitInput) 4096 := by
  have run : single unitInput unitModel = .ok () := by
    cases result : single unitInput unitModel with
    | ok value => rfl
    | error problem =>
      have control := single_accepted
      rw [result] at control
      cases control
  exact acceptsSingle_satisfiable run

/-- A false statement is rejected with its index. -/
theorem single_false_rejected :
    rejectedStatement (single unitInput "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 0\nend\n")
      = some 0 := by
  cbv

/-- A missing table is a certificate error. -/
theorem single_missing_rejected :
    certificateError (single unitInput "fang-model 1\ndomain 1\nfunction 63 0 dense 0\nend\n") = true := by
  cbv

/-- A table for a symbol that does not occur is a certificate error. -/
theorem single_unused_rejected :
    certificateError (single unitInput
      "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 1\npredicate 71 1 dense 1\nend\n") = true := by
  cbv

/-- A clause holds for every value of its variables: `p(X) | q(X)` over two elements. -/
theorem clause_accepted :
    accepted (single "cnf(a,axiom,p(X) | q(X))."
      "fang-model 1\ndomain 2\npredicate 70 1 dense 1 0\npredicate 71 1 sparse 0 1 1\nend\n") = true := by
  cbv

theorem clause_rejected :
    rejectedStatement (single "cnf(a,axiom,p(X) | q(X))."
      "fang-model 1\ndomain 2\npredicate 70 1 dense 1 0\npredicate 71 1 dense 0 0\nend\n") = some 0 := by
  cbv

/-- Quantifiers range over the domain: every element has a successor different from it. -/
theorem quantifiers_accepted :
    accepted (single "fof(a,axiom,! [X] : ? [Y] : (s(X) = Y & Y != X))."
      "fang-model 1\ndomain 2\nfunction 73 1 dense 1 0\nend\n") = true := by
  cbv

theorem quantifiers_rejected :
    rejectedStatement (single "fof(a,axiom,! [X] : ? [Y] : (s(X) = Y & Y != X))."
      "fang-model 1\ndomain 2\nfunction 73 1 dense 0 0\nend\n") = some 0 := by
  cbv

/-- A step budget of zero refuses at the first node. -/
theorem work_refused :
    (match acceptsSingle { defaultLimits with maximumWork := 0 } Fang.NativeLimits.declarationLimit
        (bytesOf unitInput) 4096 unitModel with
      | .error .work => true
      | _ => false) = true := by
  cbv

/-- Distinct objects on the bundle path: two objects need two elements. The object names keep their leading 0x00
    byte: `"x"` is 0078 and `"y"` is 0079. -/
private def objectsInput : String := "fof(a,axiom,(p(\"x\") & p(\"y\")))."

theorem objects_accepted :
    accepted (bundle objectsInput
      "fang-model 1\ndomain 2\nfunction 0078 0 dense 0\nfunction 0079 0 dense 1\npredicate 70 1 dense 1 1\nend\n")
      = true := by
  cbv

theorem objects_collide_rejected :
    (match bundle objectsInput
        "fang-model 1\ndomain 2\nfunction 0078 0 dense 1\nfunction 0079 0 dense 1\npredicate 70 1 dense 1 1\nend\n" with
      | .error .objects => true
      | _ => false) = true := by
  cbv

/-- Signed inputs: a negated conjecture is a positive input. -/
theorem inputs_accepted :
    accepted (inputs "cnf(a,axiom,p(c)).\ncnf(b,negated_conjecture,~ q(c))."
      "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 1\npredicate 71 1 dense 0\nend\n") = true := by
  cbv

theorem inputs_rejected :
    rejectedStatement (inputs "cnf(a,axiom,p(c)).\ncnf(b,negated_conjecture,~ q(c))."
      "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 1\npredicate 71 1 dense 1\nend\n") = some 1 := by
  cbv

/-- A countermodel: the premise holds and the conjecture fails; the result is the conjecture's bundle item. -/
private def goalInput : String := "fof(a,axiom,p(c)).\nfof(g,conjecture,q(c))."

theorem goal_accepted :
    goal goalInput "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 1\npredicate 71 1 dense 0\nend\n" 0
      = .ok (0, 1) := by
  cbv

theorem goal_holds_rejected :
    (match goal goalInput
        "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 1\npredicate 71 1 dense 1\nend\n" 0 with
      | .error .goalHolds => true
      | _ => false) = true := by
  cbv

theorem goal_index_rejected :
    (match goal goalInput
        "fang-model 1\ndomain 1\nfunction 63 0 dense 0\npredicate 70 1 dense 1\npredicate 71 1 dense 0\nend\n" 1 with
      | .error .noGoal => true
      | _ => false) = true := by
  cbv

/-- `! [X,Y,Z] : (p(X) => q(Y,Z))` over four elements with `p` empty. The rewritten formula is
    `(? [X] : p(X)) => ! [Z,Y] : q(Y,Z)`, decided in 6 steps; the static estimate counts 405 node evaluations. -/
private def stepInput : String := "fof(a,axiom,! [X,Y,Z] : (p(X) => q(Y,Z)))."
private def stepModel : String :=
  "fang-model 1\ndomain 4\npredicate 70 1 dense 0 0 0 0\npredicate 71 2 sparse 0 0\nend\n"

/-- The static estimate of the first version for this input and model. -/
private def staticWork (input certificate : String) : Option Nat :=
  match Integration.decodeBytesLimited Fang.NativeLimits.declarationLimit (bytesOf input) 4096 with
  | .ok values =>
    match readCertificate defaultLimits certificate (source values) with
    | .ok model => some (workOf model (source values))
    | .error _ => none
  | .error _ => none

theorem static_estimate_refuses : staticWork stepInput stepModel = some 405 := by
  cbv

theorem steps_accept :
    accepted (acceptsSingle { defaultLimits with maximumWork := 6 } Fang.NativeLimits.declarationLimit
      (bytesOf stepInput) 4096 stepModel) = true := by
  cbv

theorem steps_run_out :
    (match acceptsSingle { defaultLimits with maximumWork := 5 } Fang.NativeLimits.declarationLimit
        (bytesOf stepInput) 4096 stepModel with
      | .error .work => true
      | _ => false) = true := by
  cbv

end Fang.TptpCandidate.FullFof.Model.Controls
