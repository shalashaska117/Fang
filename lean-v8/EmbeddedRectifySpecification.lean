/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Structural specification used by the actual rectifier refinement. -/
import EmbeddedArgumentsCopy

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

inductive TermRenaming (resolve : U32 → Option U32) : fang_skolem_core.fang.syntax.Term → fang_skolem_core.fang.syntax.Term → Prop where
  | var (id fresh : U32) (binding : resolve id = some fresh) :
      TermRenaming resolve (.Var id) (.Var fresh)
  | fun_ (symbol : U32) (arguments target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
      (length : target.val.length = arguments.val.length)
      (children : ∀ i (h : i < arguments.val.length) (ht : i < target.val.length),
        TermRenaming resolve arguments.val[i] target.val[i]) :
      TermRenaming resolve (.Fun symbol arguments) (.Fun symbol target)

theorem renamedTerm_iff_renaming (stack : Bindings) (term target : fang_skolem_core.fang.syntax.Term) :
    RenamedTerm stack true term target ↔
      TermRenaming (fun id => lookupPrefix id stack.entries.val stack.active.val) term target := by
  constructor
  · intro renamed
    induction renamed with
    | var id fresh binding => exact .var id fresh binding
    | fun_ symbol args target length children ih => exact .fun_ symbol args target length ih
  · intro renamed
    induction renamed with
    | var id fresh binding => exact .var id fresh binding
    | fun_ symbol args target length children ih => exact .fun_ symbol args target length ih

def binderCount : Formula → Nat
  | .Atom _ _ | .True | .False => 0
  | .Not body => binderCount body
  | .And left right | .Or left right | .Implies left right => binderCount left + binderCount right
  | .Forall _ body | .Exists _ body => 1 + binderCount body

def binderIds : Formula → List U32
  | .Atom _ _ | .True | .False => []
  | .Not body => binderIds body
  | .And left right | .Or left right | .Implies left right => binderIds left ++ binderIds right
  | .Forall id body | .Exists id body => id :: binderIds body

def shadowResolver (resolve : U32 → Option U32) (id fresh : U32) (queried : U32) : Option U32 :=
  if id = queried then some fresh else resolve queried

/-- Fresh IDs are assigned in declaration-local preorder. A binder changes the
    resolver only inside its body. Rectification.lean proves this relation for
    the actual Rust whole-formula rectifier. -/
inductive RectifiedFormula : (U32 → Option U32) → Nat → Formula → Formula → Nat → Prop where
  | atom {resolve} (next : Nat) (predicate : U32) (arguments target : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
      (length : target.val.length = arguments.val.length)
      (children : ∀ i (h : i < arguments.val.length) (ht : i < target.val.length),
        TermRenaming resolve arguments.val[i] target.val[i]) :
      RectifiedFormula resolve next (.Atom predicate arguments) (.Atom predicate target) next
  | truth {resolve} (next) : RectifiedFormula resolve next .True .True next
  | falsity {resolve} (next) : RectifiedFormula resolve next .False .False next
  | negation {resolve first last body target} (child : RectifiedFormula resolve first body target last) :
      RectifiedFormula resolve first (.Not body) (.Not target) last
  | conjunction {resolve first middle last left right l r}
      (left_child : RectifiedFormula resolve first left l middle)
      (right_child : RectifiedFormula resolve middle right r last) :
      RectifiedFormula resolve first (.And left right) (.And l r) last
  | disjunction {resolve first middle last left right l r}
      (left_child : RectifiedFormula resolve first left l middle)
      (right_child : RectifiedFormula resolve middle right r last) :
      RectifiedFormula resolve first (.Or left right) (.Or l r) last
  | implication {resolve first middle last left right l r}
      (left_child : RectifiedFormula resolve first left l middle)
      (right_child : RectifiedFormula resolve middle right r last) :
      RectifiedFormula resolve first (.Implies left right) (.Implies l r) last
  | universal {resolve : U32 → Option U32} {first last : Nat} {id fresh : U32} {body target : Formula}
      (position : fresh.val = first)
      (child : RectifiedFormula (shadowResolver resolve id fresh)
        (first + 1) body target last) :
      RectifiedFormula resolve first (.Forall id body) (.Forall fresh target) last
  | existential {resolve : U32 → Option U32} {first last : Nat} {id fresh : U32} {body target : Formula}
      (position : fresh.val = first)
      (child : RectifiedFormula (shadowResolver resolve id fresh)
        (first + 1) body target last) :
      RectifiedFormula resolve first (.Exists id body) (.Exists fresh target) last

theorem binderIds_length (formula : Formula) : (binderIds formula).length = binderCount formula := by
  induction formula <;> simp_all [binderIds, binderCount, Nat.add_comm]

theorem rectified_counter {resolve first last source target}
    (renamed : RectifiedFormula resolve first source target last) :
    last = first + binderCount source ∧ binderCount target = binderCount source := by
  induction renamed with
  | atom | truth | falsity => simp [binderCount]
  | negation child ih => exact ih
  | conjunction left right il ir | disjunction left right il ir | implication left right il ir =>
    simp only [binderCount]
    constructor <;> omega
  | universal position child ih | existential position child ih =>
    simp only [binderCount]
    constructor <;> omega

end FangSkolemEmbeddedCore
