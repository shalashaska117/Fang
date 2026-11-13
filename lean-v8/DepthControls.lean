/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Controls only. In the Skolem core and in binder removal the formula depth
   follows the limits record: a formula nested 100 deep passes with a bound of
   1,000 and is refused with a small bound, where the product modules refuse
   every formula deeper than 64 whatever the record says. The binder-removal
   cases are those of the Rust test of the record's bound. -/
import Skolem
import BinderRemoval

namespace FangDepthControls
open Aeneas Aeneas.Std

def outcome {α : Type} (r : Result α) : Option α :=
  match r.match with
  | .ok value => some value
  | _ => none

def u32 (value : Nat) : U32 := { bv := BitVec.ofNat _ value }
def usize (value : Nat) : Usize := { bv := BitVec.ofNat _ value }

def vec {α : Type} (values : List α) : alloc.vec.Vec α :=
  if h : values.length ≤ Usize.max then alloc.vec.Vec.from values h else alloc.vec.Vec.new α

/-- `![X0] : ... : true` with `count` binders. -/
def chain : Nat → fang_binder_removal_core.fang_quantified_fof_core.Nnf
  | 0 => .True
  | count + 1 => .Forall (u32 count) (chain count)

/-- `some true` on success, `some false` on the formula depth error. -/
def removal (count bound : Nat) : Option Bool :=
  match outcome (fang_binder_removal_core.remove_universals (chain count)
      { max_formula_depth := usize bound, max_operations := usize 1000000, max_output_nodes := usize 1000000 }) with
  | some (.Ok _) => some true
  | some (.Err (.Resource .FormulaDepth)) => some false
  | _ => none

#guard removal 99 100 == some true
#guard removal 100 100 == some false
#guard removal 100 1000 == some true

/-- `~~...~p(c)` with `count` negations. -/
def negations : Nat → fang_skolem_core.fang_quantified_fof_core.Formula
  | 0 => .Atom (u32 0) (vec [.Fun (u32 0) (vec [])])
  | count + 1 => .Not (negations count)

def skolem (count bound : Nat) : Option Bool :=
  let limits : fang_skolem_core.Limits :=
    { core := { max_formula_depth := usize bound, max_formula_nodes := usize 1000000, max_term_depth := usize 64,
                max_input_term_nodes := usize 1000000, max_clauses := usize 1000000,
                max_literals_per_clause := usize 1000000, max_literals := usize 1000000,
                max_stored_nodes := usize 100000000, max_operations := usize 100000000,
                max_binders := usize 1000000 }
      max_declarations := usize 10, max_functions := usize 1000, max_skolem_symbols := usize 1000 }
  let declarations := alloc.vec.Vec.deref (vec [({ formula := negations count, positive := true } :
    fang_skolem_core.Declaration)])
  match outcome (fang_skolem_core.skolemize_problem declarations
      { functions := vec [usize 0], predicates := vec [usize 1] } limits) with
  | some (.Ok _) => some true
  | some (.Err (.Core (.Resource .FormulaDepth))) => some false
  | _ => none

#guard skolem 100 1000 == some true
#guard skolem 100 50 == some false

end FangDepthControls
