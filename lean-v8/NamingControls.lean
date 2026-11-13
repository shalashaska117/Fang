/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Controls only. Runs the generated naming entries on the cases of the Rust
   unit tests (core/tests/naming.rs) and checks the same results, so that the
   checker's copy succeeds where the Rust code does and gives the same output.
   Formulas are compared through the checker's decoding. -/
import NamingEntry

namespace FangNaming.Controls
open Aeneas Aeneas.Std fang_fof_core FangScopedFof

def outcome {α : Type} (r : Result α) : Option α :=
  match r.match with
  | .ok value => some value
  | _ => none

def u32 (value : Nat) : U32 := { bv := BitVec.ofNat _ value }
def usize (value : Nat) : Usize := { bv := BitVec.ofNat _ value }

def vec {α : Type} (values : List α) : alloc.vec.Vec α :=
  if h : values.length ≤ Usize.max then alloc.vec.Vec.from values h else alloc.vec.Vec.new α

def literal (predicate : Nat) (positive : Bool) (arguments : List fang.syntax.Term) : Nnf :=
  .Literal ⟨positive, u32 predicate, vec arguments⟩

def atom (predicate : Nat) : Nnf := literal predicate true []

/-- `p0 & p1 & ...`, nested to the left as in the Rust tests. -/
def conjunction : List Nat → Nnf
  | [] => .True
  | first :: rest => rest.foldl (fun formula predicate => .And formula (atom predicate)) (atom first)

def var (id : Nat) : fang.syntax.Term := .Var (u32 id)

/-- The default limits of the Rust clausifier, with room for the unnamed products. -/
def limits : Limits :=
  { max_formula_depth := usize 64, max_formula_nodes := usize 10000, max_term_depth := usize 64,
    max_input_term_nodes := usize 100000, max_clauses := usize 1000000, max_literals_per_clause := usize 256,
    max_literals := usize 10000000, max_stored_nodes := usize 100000000, max_operations := usize 100000000 }

def zero : Statistics := ⟨usize 0, usize 0, usize 0, usize 0, usize 0, usize 0, usize 0⟩

def same (first second : Nnf) : Bool := reprStr (decodeNnf first) == reprStr (decodeNnf second)

def renamed (formula : Nnf) (threshold next : Nat) : Option naming.Renamed :=
  match outcome (naming.name_nnf formula (usize threshold) (u32 next) limits zero) with
  | some (.Ok value) => some value
  | _ => none

def definitions (value : naming.Renamed) : List (Nat × List Nat) :=
  value.definitions.val.map fun definition => (definition.predicate.val, definition.arguments.val.map (·.val))

-- product_above_threshold_names_left_side_on_tie
#guard match renamed (.Or (conjunction [0, 1, 2]) (conjunction [3, 4, 5])) 8 10 with
  | some value =>
    same value.formula (.And (.Or (atom 10) (conjunction [3, 4, 5]))
      (.Or (literal 10 false []) (conjunction [0, 1, 2]))) &&
    definitions value == [(10, [])] && value.next.val == 11
  | none => false

-- product_at_threshold_is_copied
#guard match renamed (.Or (conjunction [0, 1, 2]) (conjunction [3, 4, 5])) 9 10 with
  | some value => same value.formula (.Or (conjunction [0, 1, 2]) (conjunction [3, 4, 5])) &&
    definitions value == [] && value.next.val == 10
  | none => false

-- larger_side_is_named
#guard match renamed (.Or (conjunction [0, 1]) (conjunction [2, 3, 4])) 2 7 with
  | some value => same value.formula (.And (.Or (conjunction [0, 1]) (atom 7))
      (.Or (literal 7 false []) (conjunction [2, 3, 4])))
  | none => false

-- side_with_one_clause_is_never_named
#guard match renamed (.Or (atom 0) (conjunction [1, 2, 3, 4, 5, 6, 7, 8, 9, 10])) 0 20 with
  | some value => same value.formula (.Or (atom 0) (conjunction [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]))
  | none => false

-- arguments_are_the_increasing_distinct_variables_of_the_body
#guard
  let left := Nnf.And (literal 0 true [var 5, .Fun (u32 1) (vec [var 2])]) (literal 1 false [var 7, var 5])
  match renamed (.Or left (.And (atom 2) (atom 3))) 3 4 with
  | some value =>
    definitions value == [(4, [2, 5, 7])] &&
    same value.formula (.And (.Or (literal 4 true [var 2, var 5, var 7]) (.And (atom 2) (atom 3)))
      (.Or (literal 4 false [var 2, var 5, var 7]) left))
  | none => false

-- nested_names_are_bottom_up_and_definitions_follow_in_order
#guard match renamed (.Or (.Or (conjunction [0, 1]) (conjunction [2, 3])) (conjunction [4, 5])) 3 6 with
  | some value =>
    value.next.val == 8 && (definitions value).map Prod.fst == [6, 7] &&
    same value.formula (.And (.And (.Or (atom 7) (conjunction [4, 5])) (.Or (literal 6 false []) (conjunction [0, 1])))
      (.Or (literal 7 false []) (.Or (atom 6) (conjunction [2, 3]))))
  | none => false

-- predicate_index_overflow_is_a_resource_error
#guard match outcome (naming.name_nnf (.Or (conjunction [0, 1, 2]) (conjunction [3, 4, 5])) (usize 8)
    (u32 4294967295) limits zero) with
  | some (.Err (.Resource .Arithmetic)) => true
  | _ => false

-- clause_count_drops_below_distribution, with five disjuncts of three atoms (243 clauses).
#guard
  let formula := [1, 2, 3, 4].foldl (fun formula block =>
    Nnf.Or formula (conjunction [3 * block, 3 * block + 1, 3 * block + 2])) (conjunction [0, 1, 2])
  match outcome (naming.name_then_clausify formula (usize 8) (u32 30) limits zero),
      outcome (nnf_entry.clausify_nnf_from formula limits zero) with
  | some (.Ok named), some (.Ok plain) => named.clauses.val.length < 40 && plain.clauses.val.length == 243
  | _, _ => false

-- without_naming_the_clauses_are_those_of_the_clausifier
#guard
  let formula := Nnf.Or (.And (atom 0) (.Or (atom 1) (atom 2))) (.Or (.And (atom 3) (atom 4)) (atom 5))
  match outcome (naming.name_then_clausify formula (usize 1000000) (u32 9) limits zero),
      outcome (nnf_entry.clausify_nnf_from formula limits zero) with
  | some (.Ok named), some (.Ok plain) =>
    reprStr (decodeClauses named.clauses.val) == reprStr (decodeClauses plain.clauses.val) &&
    named.definitions.val.length == 0 && named.next.val == 9
  | _, _ => false

end FangNaming.Controls
