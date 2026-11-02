/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedRectifyFreshness

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

theorem termRenaming_congr {resolve other : U32 → Option U32} {source target}
    (same : ∀ id, resolve id = other id) (renamed : TermRenaming resolve source target) :
    TermRenaming other source target := by
  induction renamed with
  | var id fresh binding => exact .var id fresh ((same id).symm.trans binding)
  | fun_ symbol args target length children ih => exact .fun_ symbol args target length ih

theorem rectifiedFormula_congr {resolve other : U32 → Option U32} {first last source target}
    (same : ∀ id, resolve id = other id) (renamed : RectifiedFormula resolve first source target last) :
    RectifiedFormula other first source target last := by
  induction renamed generalizing other with
  | atom next predicate args target length children =>
    exact .atom next predicate args target length (fun i hi ht => termRenaming_congr same (children i hi ht))
  | truth next => exact .truth next
  | falsity next => exact .falsity next
  | negation child ih => exact .negation (ih same)
  | conjunction left right il ir => exact .conjunction (il same) (ir same)
  | disjunction left right il ir => exact .disjunction (il same) (ir same)
  | implication left right il ir => exact .implication (il same) (ir same)
  | universal position child ih =>
    exact .universal position (ih (fun queried => by simp [shadowResolver, same queried]))
  | existential position child ih =>
    exact .existential position (ih (fun queried => by simp [shadowResolver, same queried]))

theorem pushed_formula_any (before after : Bindings) (id fresh : U32) (scope : VariableScope)
    (signature : Signature) (body : Formula) (valid : StackValid before)
    (depth : after.active.val = before.active.val + 1)
    (entries : after.entries.val = PushedEntries before { original := id, fresh }) :
    StackFormulaValid signature scope after body ↔
      FormulaValid signature (fun varId => id = varId ∨ VariableValid scope before varId) body := by
  apply formulaValid_congr
  intro varId
  unfold VariableValid
  rw [pushed_lookup before after { original := id, fresh } valid depth entries varId]
  dsimp only
  by_cases same : id = varId <;> simp [same]

theorem pushed_resolver (before after : Bindings) (id fresh : U32) (valid : StackValid before)
    (depth : after.active.val = before.active.val + 1)
    (entries : after.entries.val = PushedEntries before { original := id, fresh }) :
    (fun queried => lookupPrefix queried after.entries.val after.active.val) =
      shadowResolver (fun queried => lookupPrefix queried before.entries.val before.active.val) id fresh := by
  funext queried
  exact pushed_lookup before after { original := id, fresh } valid depth entries queried

theorem arguments_renaming_exists (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term) (stack : Bindings)
    (signature : Signature)
    (valid : ∀ i (h : i < arguments.val.length), TermValid signature .Ground stack arguments.val[i]) :
    ∃ target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term, target.val.length = arguments.val.length ∧
      ∀ i (h : i < arguments.val.length) (ht : i < target.val.length),
        RenamedTerm stack true arguments.val[i] target.val[i] := by
  classical
  have exists_target := fun i h => renamedTerm_exists (valid i h)
  let values : List fang_skolem_core.fang.syntax.Term := List.ofFn (fun i : Fin arguments.val.length => (exists_target i.val i.isLt).choose)
  have length : values.length = arguments.val.length := by simp [values]
  let target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term := alloc.vec.Vec.from values (by rw [length]; exact arguments.property)
  refine ⟨target, by simpa [target] using length, ?_⟩
  intro i hi ht
  simpa [target, values] using (exists_target i hi).choose_spec

end FangSkolemEmbeddedCore
