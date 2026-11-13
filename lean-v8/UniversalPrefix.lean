/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Ordered active-prefix correspondence for the actual universal stack. -/
import UniversalStack

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemCore
open fang_skolem_core

def universalIds (stack : Universals) : List Nat :=
  (stack.entries.val.take stack.active.val).map (fun id => id.val)

theorem universalIds_length (stack : Universals) (valid : UniversalValid stack) :
    (universalIds stack).length = stack.active.val := by
  simp only [universalIds, List.length_map, List.length_take]
  exact Nat.min_eq_left valid

theorem take_eq_of_prefix {α : Type} (left right : List α) (count : Nat)
    (same : ∀ index, index < count → left[index]? = right[index]?) :
    left.take count = right.take count := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [List.take_add_one, List.take_add_one, ih (fun index below => same index (by omega)), same count (by omega)]

theorem universalFrame_ids {before after : Universals} (frame : UniversalFrame before after) :
    universalIds after = universalIds before := by
  unfold universalIds
  rw [frame.1, take_eq_of_prefix after.entries.val before.entries.val before.active.val frame.2]

theorem universalPushedEntries_prefix (before : Universals) (id : U32)
    (valid : UniversalValid before) :
    (UniversalPushedEntries before id).take (before.active.val + 1) =
      before.entries.val.take before.active.val ++ [id] := by
  rw [List.take_add_one, take_eq_of_prefix _ _ before.active.val
    (fun index below => universalPushedEntries_lower before id index valid below),
    universalPushedEntries_top before id valid]
  rfl

theorem universals_pushed_ids {before after : Universals} (id : U32)
    (valid : UniversalValid before)
    (depth : after.active.val = before.active.val + 1)
    (entries : after.entries.val = UniversalPushedEntries before id) :
    universalIds after = universalIds before ++ [id.val] := by
  simp only [universalIds, depth, entries, universalPushedEntries_prefix before id valid,
    List.map_append, List.map_cons, List.map_nil]

/-- The term returned by the actual introduction helper has exactly the
    independent Skolem application's function ID and ordered arguments. -/
theorem introduce_decoded {before : Transformer} {binder : U32} {term : fang.syntax.Term}
    {after : Transformer} (post : IntroducePost before binder (.Ok term, after)) :
    decodeTerm term = .app before.functions.val.length
      ((universalIds before.universals).map Fang.Term.var) := by
  obtain ⟨_, _, _, _, function, arguments, dependencies, rfl, function_eq,
    arguments_eq, _, _, _, _, _⟩ := post
  simp only [decodeTerm, decodeVec_eq_map, arguments_eq, List.map_map, function_eq,
    universalIds, Function.comp_def]

end FangSkolemCore
