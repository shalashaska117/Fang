/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedStackFrame

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

/-- Signature and lexical-scope validity, independent of stack storage. -/
inductive ScopedTerm (signature : Signature) (allowed : U32 → Prop) : fang_skolem_core.fang.syntax.Term → Prop where
  | var (id : U32) (valid : allowed id) : ScopedTerm signature allowed (.Var id)
  | fun_ (symbol : U32) (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
      (arity : ArityMatches signature.functions symbol arguments.val.length)
      (children : ∀ i (h : i < arguments.val.length), ScopedTerm signature allowed arguments.val[i]) :
      ScopedTerm signature allowed (.Fun symbol arguments)

theorem termValid_iff_scoped (signature : Signature) (scope : VariableScope) (stack : Bindings)
    (term : fang_skolem_core.fang.syntax.Term) :
    TermValid signature scope stack term ↔ ScopedTerm signature (VariableValid scope stack) term := by
  constructor
  · intro valid
    induction valid with
    | var id h => exact .var id h
    | fun_ symbol args arity children ih => exact .fun_ symbol args arity ih
  · intro valid
    induction valid with
    | var id h => exact .var id h
    | fun_ symbol args arity children ih => exact .fun_ symbol args arity ih

theorem scopedTerm_congr {signature : Signature} {left right : U32 → Prop}
    (same : ∀ id, left id ↔ right id) (term : fang_skolem_core.fang.syntax.Term) :
    ScopedTerm signature left term ↔ ScopedTerm signature right term := by
  constructor
  · intro valid
    induction valid with
    | var id h => exact .var id ((same id).mp h)
    | fun_ symbol args arity children ih => exact .fun_ symbol args arity ih
  · intro valid
    induction valid with
    | var id h => exact .var id ((same id).mpr h)
    | fun_ symbol args arity children ih => exact .fun_ symbol args arity ih

def FormulaValid (signature : Signature) (allowed : U32 → Prop) : Formula → Prop
  | .Atom symbol arguments => ArityMatches signature.predicates symbol arguments.val.length ∧
      ∀ i (h : i < arguments.val.length), ScopedTerm signature allowed arguments.val[i]
  | .True | .False => True
  | .Not body => FormulaValid signature allowed body
  | .And left right | .Or left right | .Implies left right =>
      FormulaValid signature allowed left ∧ FormulaValid signature allowed right
  | .Forall id body | .Exists id body =>
      FormulaValid signature (fun varId => id = varId ∨ allowed varId) body

theorem formulaValid_congr (signature : Signature) (formula : Formula) (left right : U32 → Prop)
    (same : ∀ id, left id ↔ right id) :
    FormulaValid signature left formula ↔ FormulaValid signature right formula := by
  induction formula generalizing left right with
  | Atom symbol arguments =>
    simp only [FormulaValid]
    exact and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun _ => scopedTerm_congr same _)
  | True | False => rfl
  | Not body ih => exact ih left right same
  | And l r il ir | Or l r il ir | Implies l r il ir =>
    exact and_congr (il left right same) (ir left right same)
  | Forall id body ih | Exists id body ih =>
    exact ih _ _ (fun varId => or_congr Iff.rfl (same varId))

def StackFormulaValid (signature : Signature) (scope : VariableScope) (stack : Bindings)
    (formula : Formula) : Prop := FormulaValid signature (VariableValid scope stack) formula

theorem stackFrame_formula {before after : Bindings} (frame : StackFrame before after)
    (signature : Signature) (scope : VariableScope) (formula : Formula) :
    StackFormulaValid signature scope after formula ↔ StackFormulaValid signature scope before formula := by
  apply formulaValid_congr
  intro id
  simp only [VariableValid, stackFrame_lookup frame id]

theorem pushed_variable (before after : Bindings) (id varId : U32) (scope : VariableScope)
    (valid : StackValid before) (depth : after.active.val = before.active.val + 1)
    (entries : after.entries.val = PushedEntries before { original := id, fresh := id }) :
    VariableValid scope after varId ↔ id = varId ∨ VariableValid scope before varId := by
  unfold VariableValid
  rw [pushed_lookup before after { original := id, fresh := id } valid depth entries varId]
  dsimp only
  by_cases same : id = varId
  · simp [same]
  · simp [same]

theorem pushed_formula (before after : Bindings) (id : U32) (scope : VariableScope)
    (signature : Signature) (body : Formula) (valid : StackValid before)
    (depth : after.active.val = before.active.val + 1)
    (entries : after.entries.val = PushedEntries before { original := id, fresh := id }) :
    StackFormulaValid signature scope after body ↔
      FormulaValid signature (fun varId => id = varId ∨ VariableValid scope before varId) body := by
  apply formulaValid_congr
  intro varId
  exact pushed_variable before after id varId scope valid depth entries

end FangSkolemEmbeddedCore
