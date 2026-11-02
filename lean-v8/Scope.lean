/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedArithmetic

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core

def VariableValid (scope : VariableScope) (id : U32) : Prop :=
  match scope with
  | .Ground => False
  | .Bound count => id.val < count.val

def ArityMatches (table : alloc.vec.Vec Usize) (symbol : U32) (count : Nat) : Prop :=
  ∃ h : symbol.val < table.val.length, table.val[symbol.val].val = count

inductive TermValid (signature : Signature) (scope : VariableScope) : fang.syntax.Term → Prop where
  | var (id : U32) (valid : VariableValid scope id) : TermValid signature scope (.Var id)
  | fun_ (symbol : U32) (arguments : alloc.vec.Vec fang.syntax.Term)
      (arity : ArityMatches signature.functions symbol arguments.val.length)
      (children : ∀ i (h : i < arguments.val.length), TermValid signature scope arguments.val[i]) :
      TermValid signature scope (.Fun symbol arguments)

@[simp] theorem termValid_var (signature : Signature) (scope : VariableScope) (id : U32) :
    TermValid signature scope (.Var id) ↔ VariableValid scope id := by
  constructor
  · intro h; cases h with | var _ valid => exact valid
  · exact .var id

@[simp] theorem termValid_fun (signature : Signature) (scope : VariableScope) (symbol : U32)
    (arguments : alloc.vec.Vec fang.syntax.Term) :
    TermValid signature scope (.Fun symbol arguments) ↔
      ArityMatches signature.functions symbol arguments.val.length ∧
      ∀ i (h : i < arguments.val.length), TermValid signature scope arguments.val[i] := by
  constructor
  · intro h; cases h with | fun_ _ _ arity children => exact ⟨arity, children⟩
  · rintro ⟨arity, children⟩; exact .fun_ symbol arguments arity children

theorem variable_ground_iff_bound_zero (id : U32) :
    VariableValid .Ground id ↔ VariableValid (.Bound 0#u32) id := by
  simp [VariableValid]

theorem term_ground_iff_bound_zero (signature : Signature) (term : fang.syntax.Term) :
    TermValid signature .Ground term ↔ TermValid signature (.Bound 0#u32) term := by
  constructor
  · intro h
    induction h with
    | var id valid => exact False.elim valid
    | fun_ symbol arguments arity children ih => exact .fun_ symbol arguments arity ih
  · intro h
    induction h with
    | var id valid => exact False.elim (by simpa [VariableValid] using valid)
    | fun_ symbol arguments arity children ih => exact .fun_ symbol arguments arity ih

end FangScopedFof
