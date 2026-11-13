/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedCnfInvariant

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core
variable {signature : Signature} {scope : VariableScope}
set_option maxRecDepth 2048

def NnfScoped (signature : Signature) (scope : VariableScope) : Nnf → Prop
  | .Literal literal => (LiteralScoped signature scope) literal
  | .True | .False => True
  | .And left right | .Or left right => (NnfScoped signature scope) left ∧ (NnfScoped signature scope) right

theorem singleton_spec {α : Type} (value : α) :
    fang_fof_core.singleton value ⦃ fun output => output.val = [value] ⦄ := by
  unfold fang_fof_core.singleton
  apply spec_mono (alloc.vec.Vec.push_spec (alloc.vec.Vec.new α) value (by simp; scalar_tac))
  intro output same
  simpa using same

/-- Exact raw clause order, groundness and width bounds for the generated recursive function. -/
theorem clausify_nnf_spec (formula : Nnf) (ground : (NnfScoped signature scope) formula)
    (limits : Limits) (work : Work) :
    clausify_nnf formula limits work ⦃ CnfPost (fun output => (CnfScoped signature scope) output ∧
      decodeClauses output.clauses.val = (decodeNnf formula).clauses) work ⦄ := by
  induction formula generalizing work with
  | Literal literal | True | False | And left right ihl ihr | Or left right ihl ihr =>
    unfold clausify_nnf
    apply spec_bind (tick_spec work limits)
    intro answer ticked
    unfold TickAnswer at ticked
    split at ticked
    next fits =>
      obtain ⟨operation, rfl, operation_eq⟩ := ticked
      simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      let work1 : Work := {statistics := {work.statistics with operations := operation}}
      first
      | -- Truth has no clauses and needs no storage.
        simp [CnfPost, CnfChecked, CnfScoped, decodeClauses, clauseLists,
          decodeNnf, Fang.GroundFOF.Nnf.clauses] <;> omega
      | -- Both recursive branches preserve their left-to-right clause order.
        apply spec_bind (ihl ground.1 work1)
        rintro ⟨leftResult, work2⟩ ⟨hm, hp⟩
        dsimp only at hm hp
        simp only [Aeneas.Std.uncurry]
        cases leftResult with
        | Err error =>
          cases error with
          | Invalid invalid => exact False.elim hp
          | Resource kind =>
            simpa [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked] using
              (show work.statistics.operations.val ≤ work2.statistics.operations.val ∧ CnfResource kind from
                ⟨by dsimp [work1] at hm; omega, hp⟩)
        | Ok leftCnf =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          apply spec_bind (ihr ground.2 work2)
          rintro ⟨rightResult, work3⟩ ⟨hm2, hp2⟩
          dsimp only at hm2 hp2
          simp only [Aeneas.Std.uncurry]
          cases rightResult with
          | Err error =>
            cases error with
            | Invalid invalid => exact False.elim hp2
            | Resource kind =>
              simpa [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked] using
                (show work.statistics.operations.val ≤ work3.statistics.operations.val ∧ CnfResource kind from
                  ⟨by dsimp [work1] at hm; omega, hp2⟩)
          | Ok rightCnf =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            first
            | apply spec_mono (append_cnf_refinement leftCnf rightCnf hp.1 hp2.1 limits work3)
              rintro ⟨result, after⟩ ⟨hm3, hp3⟩
              refine ⟨by dsimp [work1] at hm; omega, ?_⟩
              cases result with
              | Err error => cases error <;> exact hp3
              | Ok output =>
                refine ⟨hp3.1, ?_⟩
                simpa [decodeNnf, Fang.GroundFOF.Nnf.clauses, hp.2, hp2.2] using hp3.2
            | apply spec_mono (product_cnf_refinement leftCnf rightCnf hp.1 hp2.1 limits work3)
              rintro ⟨result, after⟩ ⟨hm3, hp3⟩
              refine ⟨by dsimp [work1] at hm; omega, ?_⟩
              cases result with
              | Err error => cases error <;> exact hp3
              | Ok output =>
                refine ⟨hp3.1, ?_⟩
                simpa [decodeNnf, Fang.GroundFOF.Nnf.clauses, hp.2, hp2.2] using hp3.2
      | -- Falsity and a literal first check the output shape and allocate a clause.
        apply spec_bind (check_shape_spec _ _ _ limits)
        intro answer shape
        cases answer with
        | Err error =>
          cases error with
          | Invalid invalid => exact False.elim shape
          | Resource kind =>
            simpa [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked] using
              (show work.statistics.operations.val ≤ operation.val ∧ CnfResource kind from ⟨by omega, shape⟩)
        | Ok checked =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          apply spec_bind (allocate_spec work1 1#usize limits)
          intro answer allocated
          unfold AllocationAnswer at allocated
          split at allocated
          next fitsAllocation =>
            obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
            simp only [Aeneas.Std.uncurry, bind_ok]
            let work2 : Work := {statistics := {work.statistics with operations := operation, allocated_nodes := nodes}}
            first
            | -- False is exactly one empty clause.
              apply spec_bind (singleton_spec (alloc.vec.Vec.new fang.syntax.Literal))
              intro clauses same
              simp [CnfPost, CnfChecked, CnfScoped, decodeClauses, clauseLists,
                decodeNnf, Fang.GroundFOF.Nnf.clauses, same, work1, work2] <;> omega
            | -- The accounting lower bound discharges both raw machine subtractions.
              apply spec_bind (spec_and (copy_literal_spec literal ground limits work2)
                (copy_literal_allocation literal ground limits work2))
              rintro ⟨result, after⟩ ⟨⟨hm, hp⟩, allocation⟩
              dsimp only at hm hp
              simp -failIfUnchanged only [Aeneas.Std.uncurry]
              cases result with
              | Err error =>
                cases error with
                | Invalid invalid => exact False.elim hp
                | Resource kind =>
                  simpa [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CnfPost, CnfChecked] using
                    (show work.statistics.operations.val ≤ after.statistics.operations.val ∧ CnfResource kind from
                      ⟨by dsimp [work2] at hm; omega, Or.inl hp⟩)
              | Ok copied =>
                subst copied
                simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
                have grown : nodes.val + 1 ≤ after.statistics.allocated_nodes.val := allocation.2
                apply spec_bind (Usize.sub_spec (x := after.statistics.allocated_nodes) (y := nodes) (by omega))
                intro difference difference_eq
                have difference_val : difference.val = after.statistics.allocated_nodes.val - nodes.val := difference_eq.1
                apply spec_bind (Usize.sub_spec (x := difference) (y := 1#usize) (by change 1 ≤ difference.val; omega))
                intro terms terms_eq
                apply spec_bind (singleton_spec literal)
                intro clause clause_eq
                apply spec_bind (singleton_spec clause)
                intro clauses clauses_eq
                simp only [spec_ok, CnfPost, CnfChecked]
                refine ⟨by dsimp [work2] at hm; omega, ?_, ?_⟩
                · constructor
                  · intro candidate hc entry he
                    simp only [clauses_eq, List.mem_singleton] at hc
                    subst candidate
                    simp only [clause_eq, List.mem_singleton] at he
                    subst entry
                    exact ground
                  · intro candidate hc
                    simp only [clauses_eq, List.mem_singleton] at hc
                    subst candidate
                    simp [clause_eq]
                · simp [decodeClauses, clauseLists, clauses_eq, clause_eq, decodeNnf,
                    Fang.GroundFOF.Nnf.clauses]
          next exceedsAllocation =>
            rw [allocated]
            simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              CnfPost, CnfChecked, CnfResource, CopyResource, work1] using
              (show work.statistics.operations.val ≤ operation.val by omega)
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        CnfPost, CnfChecked, CnfResource, CopyResource]

end FangScopedFof
