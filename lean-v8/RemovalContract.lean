/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RemovalSyntax

open Aeneas Aeneas.Std Aeneas.Std.WP Result
namespace FangBinderRemovalCore
open fang_binder_removal_core

def Counters (limits : Limits) (before after : Statistics) : Prop :=
  before.operations.val ≤ after.operations.val ∧
  before.output_nodes.val ≤ after.output_nodes.val ∧
  after.operations.val ≤ max before.operations.val limits.max_operations.val ∧
  after.output_nodes.val ≤ max before.output_nodes.val limits.max_output_nodes.val

theorem counters_refl (limits : Limits) (before : Statistics) : Counters limits before before := by
  simp [Counters]

theorem counters_trans {limits before middle after}
    (first : Counters limits before middle) (second : Counters limits middle after) :
    Counters limits before after := by
  unfold Counters at *
  omega

def ErrorMeaning (source : Input) : fang_binder_removal_core.Error → Prop
  | .Resource _ => True
  | .ResidualExistential id => HasExistential id source

def RemovalPost (source : Input) (limits : Limits) (before : Statistics)
    (answer : core.result.Result Output fang_binder_removal_core.Error × Statistics) : Prop :=
  Counters limits before answer.2 ∧
  match answer.1 with
  | .Ok target => Erased source target ∧
      answer.2.operations.val = before.operations.val + inputNodes source ∧
      answer.2.output_nodes.val = before.output_nodes.val + outputNodes target
  | .Err error => ErrorMeaning source error

theorem resource_post (source : Input) (limits : Limits) (before after : Statistics)
    (kind : Resource) (counters : Counters limits before after) :
    RemovalPost source limits before (.Err (.Resource kind), after) := ⟨counters, trivial⟩

end FangBinderRemovalCore
