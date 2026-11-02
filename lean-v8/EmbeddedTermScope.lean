/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedNameLookup

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

def OuterValid (scope : VariableScope) (id : U32) : Prop :=
  match scope with
  | .Ground => False
  | .Bound count => id.val < count.val

def VariableValid (scope : VariableScope) (stack : Bindings) (id : U32) : Prop :=
  (lookupPrefix id stack.entries.val stack.active.val).isSome = true ∨ OuterValid scope id

def ArityMatches (table : alloc.vec.Vec Usize) (symbol : U32) (count : Nat) : Prop :=
  ∃ h : symbol.val < table.val.length, table.val[symbol.val].val = count

inductive TermValid (signature : Signature) (scope : VariableScope) (stack : Bindings) : fang_skolem_core.fang.syntax.Term → Prop where
  | var (id : U32) (valid : VariableValid scope stack id) : TermValid signature scope stack (.Var id)
  | fun_ (symbol : U32) (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
      (arity : ArityMatches signature.functions symbol arguments.val.length)
      (children : ∀ i (h : i < arguments.val.length), TermValid signature scope stack arguments.val[i]) :
      TermValid signature scope stack (.Fun symbol arguments)

@[simp] theorem termValid_var (signature : Signature) (scope : VariableScope) (stack : Bindings) (id : U32) :
    TermValid signature scope stack (.Var id) ↔ VariableValid scope stack id := by
  constructor
  · intro h; cases h with | var _ valid => exact valid
  · exact .var id

@[simp] theorem termValid_fun (signature : Signature) (scope : VariableScope) (stack : Bindings) (symbol : U32)
    (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term) :
    TermValid signature scope stack (.Fun symbol arguments) ↔
      ArityMatches signature.functions symbol arguments.val.length ∧
      ∀ i (h : i < arguments.val.length), TermValid signature scope stack arguments.val[i] := by
  constructor
  · intro h; cases h with | fun_ _ _ arity children => exact ⟨arity, children⟩
  · rintro ⟨arity, children⟩; exact .fun_ symbol arguments arity children


end FangSkolemEmbeddedCore
