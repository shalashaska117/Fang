/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedCnf

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core
variable {signature : Signature} {scope : VariableScope}

def decodeClauses (clauses : List (alloc.vec.Vec fang.syntax.Literal)) : Fang.Problem :=
  (clauseLists clauses).map (List.map decodeLiteral)

theorem decodeClauses_append (left right : List (alloc.vec.Vec fang.syntax.Literal)) :
    decodeClauses (left ++ right) = decodeClauses left ++ decodeClauses right := by
  simp [decodeClauses, clauseLists, List.map_append]

theorem decode_rawProduct (left right : List (alloc.vec.Vec fang.syntax.Literal)) :
    (rawProduct left right).map (List.map decodeLiteral) =
      Fang.GroundFOF.clauseProduct (decodeClauses left) (decodeClauses right) := by
  simp [rawProduct, decodeClauses, clauseLists, Fang.GroundFOF.clauseProduct,
    List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

theorem append_cnf_semantics (left right : Cnf)
    (leftGround : ∀ i (h : i < left.clauses.val.length), (ClauseScoped signature scope) left.clauses.val[i])
    (rightGround : ∀ i (h : i < right.clauses.val.length), (ClauseScoped signature scope) right.clauses.val[i])
    (limits : Limits) (work : Work) {D : Type} (model : Fang.Interpretation D) (valuation : Nat → D) :
    append_cnf left right limits work ⦃ CnfPost (fun value =>
      decodeClauses value.clauses.val = decodeClauses left.clauses.val ++ decodeClauses right.clauses.val ∧
      (Fang.GroundFOF.HoldsAt model valuation (decodeClauses value.clauses.val) ↔
        Fang.GroundFOF.HoldsAt model valuation (decodeClauses left.clauses.val) ∧
        Fang.GroundFOF.HoldsAt model valuation (decodeClauses right.clauses.val))) work ⦄ := by
  apply spec_mono (append_cnf_spec left right leftGround rightGround limits work)
  rintro ⟨answer, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases answer with
  | Err error => cases error <;> exact hp
  | Ok value =>
    have exactClauses : decodeClauses value.clauses.val =
        decodeClauses left.clauses.val ++ decodeClauses right.clauses.val := by
      rw [hp.1, decodeClauses_append]
    refine ⟨exactClauses, ?_⟩
    rw [exactClauses]
    exact Fang.GroundFOF.append_holdsAt model valuation _ _

theorem product_cnf_semantics (left right : Cnf)
    (leftGround : ∀ i (h : i < left.clauses.val.length), (ClauseScoped signature scope) left.clauses.val[i])
    (rightGround : ∀ i (h : i < right.clauses.val.length), (ClauseScoped signature scope) right.clauses.val[i])
    (leftWidth : ∀ i (h : i < left.clauses.val.length), left.clauses.val[i].val.length ≤ left.max_width.val)
    (rightWidth : ∀ i (h : i < right.clauses.val.length), right.clauses.val[i].val.length ≤ right.max_width.val)
    (limits : Limits) (work : Work) {D : Type} (model : Fang.Interpretation D) (valuation : Nat → D) :
    product_cnf left right limits work ⦃ CnfPost (fun value =>
      decodeClauses value.clauses.val = Fang.GroundFOF.clauseProduct
        (decodeClauses left.clauses.val) (decodeClauses right.clauses.val) ∧
      (Fang.GroundFOF.HoldsAt model valuation (decodeClauses value.clauses.val) ↔
        Fang.GroundFOF.HoldsAt model valuation (decodeClauses left.clauses.val) ∨
        Fang.GroundFOF.HoldsAt model valuation (decodeClauses right.clauses.val))) work ⦄ := by
  apply spec_mono (product_cnf_spec left right leftGround rightGround leftWidth rightWidth limits work)
  rintro ⟨answer, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases answer with
  | Err error => cases error <;> exact hp
  | Ok value =>
    have exactClauses : decodeClauses value.clauses.val = Fang.GroundFOF.clauseProduct
        (decodeClauses left.clauses.val) (decodeClauses right.clauses.val) := by
      unfold decodeClauses
      rw [hp.1, decode_rawProduct]
      rfl
    refine ⟨exactClauses, ?_⟩
    rw [exactClauses]
    exact Fang.GroundFOF.clauseProduct_holdsAt model valuation _ _

end FangScopedFof
