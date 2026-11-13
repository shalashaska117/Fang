/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedTermCopy

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

theorem renamedTerm_identity {signature : Signature} {scope : VariableScope} {stack : Bindings}
    {term : fang_skolem_core.fang.syntax.Term} (valid : TermValid signature scope stack term) :
    RenamedTerm stack false term term := by
  induction valid with
  | var id member => exact .var id id rfl
  | fun_ symbol arguments arity children ih => exact .fun_ symbol arguments arguments rfl (fun i h _ => ih i h)

/-- Closed lexical validation provides a target for the renaming relation.
    Choice here constructs a mathematical witness, not an executable algorithm. -/
theorem renamedTerm_exists {signature : Signature} {stack : Bindings}
    {term : fang_skolem_core.fang.syntax.Term} (valid : TermValid signature .Ground stack term) :
    ∃ target, RenamedTerm stack true term target := by
  classical
  induction valid with
  | var id member =>
    have present : (lookupPrefix id stack.entries.val stack.active.val).isSome = true := by
      simpa [VariableValid, OuterValid] using member
    cases found : lookupPrefix id stack.entries.val stack.active.val with
    | none => simp [found] at present
    | some fresh => exact ⟨.Var fresh, .var id fresh found⟩
  | fun_ symbol arguments arity children ih =>
    let values : List fang_skolem_core.fang.syntax.Term := List.ofFn (fun i : Fin arguments.val.length => (ih i.val i.isLt).choose)
    have length : values.length = arguments.val.length := by simp [values]
    let target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term := alloc.vec.Vec.from values (by rw [length]; exact arguments.property)
    refine ⟨.Fun symbol target, .fun_ symbol arguments target (by simpa [target] using length) ?_⟩
    intro i hi ht
    simpa [target, values] using (ih i hi).choose_spec

theorem renamedTerm_functional {stack : Bindings} {rectify : Bool} {term left right : fang_skolem_core.fang.syntax.Term}
    (first : RenamedTerm stack rectify term left) (second : RenamedTerm stack rectify term right) : left = right := by
  induction first generalizing right with
  | var id fresh binding =>
    cases second with
    | var _ other other_binding =>
      have same : fresh = other := by
        cases rectify with
        | false => simp only [Bool.false_eq_true, ite_false] at binding other_binding; exact binding.trans other_binding.symm
        | true => simp only [ite_true] at binding other_binding; rw [binding] at other_binding; exact Option.some.inj other_binding
      rw [same]
  | fun_ symbol arguments target length children ih =>
    cases second with
    | fun_ _ _ other other_length other_children =>
      congr 1
      apply alloc.vec.Vec.ext
      apply List.ext_getElem
      · omega
      · intro i ht ho
        exact ih i (by omega) ht (other_children i (by omega) ho)

theorem copy_identity_spec (term : fang_skolem_core.fang.syntax.Term) (stack : Bindings)
    {signature : Signature} {scope : VariableScope} (term_valid : TermValid signature scope stack term)
    (stack_valid : StackValid stack) (limits : Limits) (work : Work) :
    copy_term term stack false limits work ⦃ CopyPost (fun value => value = term) work ⦄ :=
  copy_term_spec term term stack false (renamedTerm_identity term_valid) stack_valid limits work

theorem copy_closed_spec (term : fang_skolem_core.fang.syntax.Term) (stack : Bindings)
    {signature : Signature} (term_valid : TermValid signature .Ground stack term)
    (stack_valid : StackValid stack) (limits : Limits) (work : Work) :
    copy_term term stack true limits work ⦃ CopyPost (RenamedTerm stack true term) work ⦄ := by
  obtain ⟨target, renamed⟩ := renamedTerm_exists term_valid
  apply spec_mono (copy_term_spec term target stack true renamed stack_valid limits work)
  rintro ⟨result, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases result with
  | Ok value => rw [hp]; exact renamed
  | Err error => cases error <;> exact hp

end FangSkolemEmbeddedCore
