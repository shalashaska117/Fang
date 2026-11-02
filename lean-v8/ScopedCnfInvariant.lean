/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedCnfSemantics
import ScopedCopyAllocation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core
variable {signature : Signature} {scope : VariableScope}

/-- Scoped argument validity and a width bound; literal and term counters are not specified here. -/
def CnfScoped (signature : Signature) (scope : VariableScope) (value : Cnf) : Prop :=
  (∀ clause ∈ value.clauses.val, ∀ literal ∈ clause.val, (LiteralScoped signature scope) literal) ∧
  (∀ clause ∈ value.clauses.val, clause.val.length ≤ value.max_width.val)

theorem cnfValid_scoped (value : Cnf) (valid : (CnfScoped signature scope) value) :
    ∀ i (h : i < value.clauses.val.length), (ClauseScoped signature scope) value.clauses.val[i] := by
  intro i hi j hj
  exact valid.1 _ (List.getElem_mem hi) _ (List.getElem_mem hj)

theorem cnfValid_width (value : Cnf) (valid : (CnfScoped signature scope) value) :
    ∀ i (h : i < value.clauses.val.length), value.clauses.val[i].val.length ≤ value.max_width.val := by
  intro i hi
  exact valid.2 _ (List.getElem_mem hi)

theorem append_cnf_refinement (left right : Cnf) (leftValid : (CnfScoped signature scope) left) (rightValid : (CnfScoped signature scope) right)
    (limits : Limits) (work : Work) :
    append_cnf left right limits work ⦃ CnfPost (fun value => (CnfScoped signature scope) value ∧
      decodeClauses value.clauses.val = decodeClauses left.clauses.val ++ decodeClauses right.clauses.val) work ⦄ := by
  apply spec_mono (append_cnf_spec left right (cnfValid_scoped left leftValid) (cnfValid_scoped right rightValid) limits work)
  rintro ⟨answer, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases answer with
  | Err error => cases error <;> exact hp
  | Ok value =>
    rcases hp with ⟨lists, literals, terms, width⟩
    constructor
    · constructor
      · intro clause hc literal hl
        rw [lists] at hc
        cases List.mem_append.mp hc with
        | inl hc => exact leftValid.1 _ hc _ hl
        | inr hc => exact rightValid.1 _ hc _ hl
      · intro clause hc
        rw [lists] at hc
        rw [width]
        cases List.mem_append.mp hc with
        | inl hc => exact Nat.le_trans (leftValid.2 _ hc) (Nat.le_max_left _ _)
        | inr hc => exact Nat.le_trans (rightValid.2 _ hc) (Nat.le_max_right _ _)
    · rw [lists, decodeClauses_append]

theorem product_cnf_refinement (left right : Cnf) (leftValid : (CnfScoped signature scope) left) (rightValid : (CnfScoped signature scope) right)
    (limits : Limits) (work : Work) :
    product_cnf left right limits work ⦃ CnfPost (fun value => (CnfScoped signature scope) value ∧
      decodeClauses value.clauses.val = Fang.GroundFOF.clauseProduct
        (decodeClauses left.clauses.val) (decodeClauses right.clauses.val)) work ⦄ := by
  apply spec_mono (product_cnf_spec left right (cnfValid_scoped left leftValid) (cnfValid_scoped right rightValid)
    (cnfValid_width left leftValid) (cnfValid_width right rightValid) limits work)
  rintro ⟨answer, after⟩ ⟨hm, hp⟩
  refine ⟨hm, ?_⟩
  cases answer with
  | Err error => cases error <;> exact hp
  | Ok value =>
    rcases hp with ⟨lists, counters⟩
    have membership : ∀ clause ∈ value.clauses.val,
        ∃ leftClause ∈ left.clauses.val, ∃ rightClause ∈ right.clauses.val,
          clause.val = leftClause.val ++ rightClause.val := by
      intro clause hc
      have hlist : clause.val ∈ rawProduct left.clauses.val right.clauses.val := by
        rw [← lists]
        exact List.mem_map.mpr ⟨clause, hc, rfl⟩
      obtain ⟨leftClause, hl, hr⟩ := List.mem_flatMap.mp hlist
      obtain ⟨rightClause, hr, heq⟩ := List.mem_map.mp hr
      exact ⟨leftClause, hl, rightClause, hr, heq.symm⟩
    constructor
    · constructor
      · intro clause hc literal hLiteral
        obtain ⟨leftClause, hl, rightClause, hr, heq⟩ := membership clause hc
        rw [heq] at hLiteral
        cases List.mem_append.mp hLiteral with
        | inl hLiteral => exact leftValid.1 _ hl _ hLiteral
        | inr hLiteral => exact rightValid.1 _ hr _ hLiteral
      · intro clause hc
        obtain ⟨leftClause, hl, rightClause, hr, heq⟩ := membership clause hc
        have nonempty : left.clauses.val.length * right.clauses.val.length ≠ 0 := by
          have hleft := List.length_pos_of_mem hl
          have hright := List.length_pos_of_mem hr
          exact Nat.ne_of_gt (Nat.mul_pos hleft hright)
        rw [ite_eq_right nonempty] at counters
        rw [heq, List.length_append, counters.2.2]
        exact Nat.add_le_add (leftValid.2 _ hl) (rightValid.2 _ hr)
    · unfold decodeClauses
      rw [lists, decode_rawProduct]
      rfl

end FangScopedFof
