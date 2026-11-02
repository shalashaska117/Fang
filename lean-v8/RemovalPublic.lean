/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RemovalProof

open Aeneas Aeneas.Std Aeneas.Std.WP Result
namespace FangBinderRemovalCore
open fang_binder_removal_core

def PublicPost (source : Input) (limits : Limits)
    (answer : core.result.Result Removed fang_binder_removal_core.Error) : Prop :=
  match answer with
  | .Ok result => Erased source result.formula ∧
      result.statistics.operations.val = inputNodes source ∧
      result.statistics.output_nodes.val = outputNodes result.formula ∧
      result.statistics.operations.val ≤ limits.max_operations.val ∧
      result.statistics.output_nodes.val ≤ limits.max_output_nodes.val
  | .Err error => ErrorMeaning source error

/-- Totality and exact success syntax/counters of the actual public Rust model.
    Resource outcomes do not imply that an input is logically invalid. -/
theorem remove_universals_spec (source : Input) (limits : Limits) :
    remove_universals source limits ⦃ PublicPost source limits ⦄ := by
  unfold remove_universals
  apply spec_bind (remove_spec source 1#usize limits { operations := 0#usize, output_nodes := 0#usize })
  rintro ⟨answer, after⟩ ⟨counters, outcome⟩
  dsimp only at counters outcome
  simp only [Aeneas.Std.uncurry]
  cases answer with
  | Err error =>
    simpa [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, PublicPost] using outcome
  | Ok result =>
    obtain ⟨erased, operations, nodes⟩ := outcome
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, spec_ok, PublicPost]
    refine ⟨erased, ?_, ?_, ?_, ?_⟩
    · simpa using operations
    · simpa using nodes
    · simpa [Counters] using counters.2.2.1
    · simpa [Counters] using counters.2.2.2

theorem remove_universals_success {source limits result}
    (success : remove_universals source limits = .ok (.Ok result)) :
    Erased source result.formula ∧
      result.statistics.operations.val = inputNodes source ∧
      result.statistics.output_nodes.val = outputNodes result.formula ∧
      result.statistics.operations.val ≤ limits.max_operations.val ∧
      result.statistics.output_nodes.val ≤ limits.max_output_nodes.val := by
  have checked := remove_universals_spec source limits
  rw [success] at checked
  simpa only [spec_ok, PublicPost] using checked

theorem remove_universals_count {source limits result}
    (success : remove_universals source limits = .ok (.Ok result)) :
    result.statistics.operations.val = result.statistics.output_nodes.val + universals source := by
  obtain ⟨erased, operations, nodes, _, _⟩ := remove_universals_success success
  rw [operations, nodes]
  exact erased.node_count

end FangBinderRemovalCore
