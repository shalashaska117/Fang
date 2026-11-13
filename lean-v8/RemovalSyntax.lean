/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RemovalResources

namespace FangBinderRemovalCore
open fang_binder_removal_core
abbrev Input := fang_quantified_fof_core.Nnf
abbrev Output := fang_fof_core.Nnf

/-- Exact ordered erasure over the generated types; literal values are identical. -/
inductive Erased : Input → Output → Prop where
  | literal (value) : Erased (.Literal value) (.Literal value)
  | truth : Erased .True .True
  | falsity : Erased .False .False
  | and_ {left right l r} : Erased left l → Erased right r → Erased (.And left right) (.And l r)
  | or_ {left right l r} : Erased left l → Erased right r → Erased (.Or left right) (.Or l r)
  | forall_ {id body result} : Erased body result → Erased (.Forall id body) result

def inputNodes : Input → Nat
  | .Literal _ | .True | .False => 1
  | .And left right | .Or left right => 1 + inputNodes left + inputNodes right
  | .Forall _ body | .Exists _ body => 1 + inputNodes body

def outputNodes : Output → Nat
  | .Literal _ | .True | .False => 1
  | .And left right | .Or left right => 1 + outputNodes left + outputNodes right

def universals : Input → Nat
  | .Literal _ | .True | .False => 0
  | .And left right | .Or left right => universals left + universals right
  | .Forall _ body => 1 + universals body
  | .Exists _ body => universals body

def HasExistential (id : Aeneas.Std.U32) : Input → Prop
  | .Literal _ | .True | .False => False
  | .And left right | .Or left right => HasExistential id left ∨ HasExistential id right
  | .Forall _ body => HasExistential id body
  | .Exists binder body => binder = id ∨ HasExistential id body

theorem Erased.functional {source left right} (first : Erased source left)
    (second : Erased source right) : left = right := by
  induction first generalizing right with
  | literal | truth | falsity => cases second; rfl
  | and_ a b ia ib => cases second with | and_ c d => rw [ia c, ib d]
  | or_ a b ia ib => cases second with | or_ c d => rw [ia c, ib d]
  | forall_ child ih => cases second with | forall_ other => exact ih other

theorem Erased.node_count {source target} (erased : Erased source target) :
    inputNodes source = outputNodes target + universals source := by
  induction erased <;> simp_all [inputNodes, outputNodes, universals] <;> omega

end FangBinderRemovalCore
