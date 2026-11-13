/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Freshness properties composed with the actual rectifier in PublicRectification. -/
import EmbeddedRectifySpecification

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

theorem rectified_binder_ids {resolve first last source target}
    (renamed : RectifiedFormula resolve first source target last) :
    (binderIds target).map UScalar.val = List.range' first (binderCount source) := by
  induction renamed with
  | atom | truth | falsity => simp [binderIds, binderCount]
  | negation child ih => exact ih
  | conjunction left right il ir | disjunction left right il ir | implication left right il ir =>
    simp [binderIds, binderCount, il, ir, (rectified_counter left).1]
  | universal position child ih | existential position child ih =>
    simp only [binderIds, List.map_cons, position, ih, binderCount]
    rw [Nat.add_comm 1, List.range'_succ]

theorem rectified_binders_unique {resolve first last source target}
    (renamed : RectifiedFormula resolve first source target last) :
    (binderIds target).Nodup := by
  have distinct := List.nodup_range' (s := first) (n := binderCount source)
  rw [← rectified_binder_ids renamed] at distinct
  exact distinct.of_map

theorem rectified_binder_interval {resolve first last source target id}
    (renamed : RectifiedFormula resolve first source target last)
    (occurs : id ∈ binderIds target) : first ≤ id.val ∧ id.val < last := by
  have inside : id.val ∈ (binderIds target).map UScalar.val := List.mem_map.mpr ⟨id, occurs, rfl⟩
  rw [rectified_binder_ids renamed, List.mem_range'_1] at inside
  have counter := (rectified_counter renamed).1
  omega

end FangSkolemEmbeddedCore
