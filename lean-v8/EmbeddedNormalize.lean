/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import EmbeddedRepresentation

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangSkolemEmbeddedCore
open fang_skolem_core.fang_quantified_fof_core

theorem valid_atom_scoped (signature : Signature) (allowed : U32 → Prop) (predicate : U32)
    (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term) (valid : FormulaValid signature allowed (.Atom predicate arguments)) :
    ∀ i (h : i < (alloc.vec.Vec.deref arguments).val.length),
      ScopedTerm signature allowed (alloc.vec.Vec.deref arguments).val[i] := by
  intro i hi
  simp [alloc.vec.Vec.deref] at hi ⊢
  exact valid.2 i hi

theorem normalize_atom_spec (predicate : U32) (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term)
    (signature : Signature) (allowed : U32 → Prop) (valid : FormulaValid signature allowed (.Atom predicate arguments))
    (positive : Bool) (limits : Limits) (work : Work) :
    normalize_formula (.Atom predicate arguments) positive limits work
      ⦃ CopyPost (fun value => decodeNnf value = (decodeFormula (.Atom predicate arguments)).nnf positive) work ⦄ := by
  unfold normalize_formula
  apply spec_bind (tick_spec work limits)
  intro answer ticked
  unfold TickAnswer at ticked
  split at ticked
  next fits =>
    obtain ⟨operation, rfl, operation_eq⟩ := ticked
    simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    let work1 : Work := {statistics := {work.statistics with operations := operation}}
    apply spec_bind (allocate_spec work1 1#usize limits)
    intro answer allocated
    unfold AllocationAnswer at allocated
    split at allocated
    next fitsAllocation =>
      obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
      simp only [Aeneas.Std.uncurry, bind_ok]
      let work2 : Work := {statistics := {work.statistics with operations := operation, allocated_nodes := nodes}}
      have ground : ∀ i (h : i < (alloc.vec.Vec.deref arguments).val.length),
          ScopedTerm signature allowed (alloc.vec.Vec.deref arguments).val[i] :=
        valid_atom_scoped signature allowed predicate arguments valid
      apply spec_bind bindings_new_spec
      intro stack ⟨stack_valid, _, _⟩
      apply spec_bind (copy_arguments_spec (alloc.vec.Vec.deref arguments) arguments stack false limits
        stack_valid (by simp [alloc.vec.Vec.deref]) (fun i hi ht => by
          simpa [alloc.vec.Vec.deref] using scoped_identity_copy (ground i hi) stack) work2)
      rintro ⟨result, after⟩ ⟨hm, hp⟩
      dsimp only at hm hp
      cases result with
      | Ok copied =>
        subst copied
        simpa [core.result.Result.Insts.CoreOpsTry.branch, CopyPost, decodeNnf,
          decodeLiteral, decodeFormula, Fang.QuantifiedFOF.Formula.nnf] using
          (show work.statistics.operations.val ≤ after.statistics.operations.val by dsimp [work2] at hm; omega)
      | Err error =>
        have post : CopyPost (fun value => decodeNnf value = (decodeFormula (.Atom predicate arguments)).nnf positive)
            work (.Err error, after) := by
          refine ⟨by dsimp only; dsimp [work2] at hm; omega, ?_⟩
          cases error <;> exact hp
        simpa [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual] using post
    next exceedsAllocation =>
      rw [allocated]
      simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource, work1] using
        (show work.statistics.operations.val ≤ operation.val by omega)
  next exceedsOperations =>
    rw [ticked]
    simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource]

theorem normalize_formula_spec (formula : Formula) (signature : Signature) (allowed : U32 → Prop)
    (valid : FormulaValid signature allowed formula) (positive : Bool) (limits : Limits) (work : Work) :
    normalize_formula formula positive limits work
      ⦃ CopyPost (fun value => decodeNnf value = (decodeFormula formula).nnf positive) work ⦄ := by
  induction formula generalizing allowed positive work with
  | Atom predicate arguments => exact normalize_atom_spec predicate arguments signature allowed valid positive limits work
  | True | False | Not inner ih | And left right ihl ihr
    | Or left right ihl ihr | Implies left right ihl ihr
    | Forall id body ih | Exists id body ih =>
    unfold normalize_formula
    apply spec_bind (tick_spec work limits)
    intro answer ticked
    unfold TickAnswer at ticked
    split at ticked
    next fits =>
      obtain ⟨operation, rfl, operation_eq⟩ := ticked
      simp only [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      let work1 : Work := {statistics := {work.statistics with operations := operation}}
      first
      | -- Negation consumes a tick but allocates no NNF node.
        apply spec_mono (ih allowed valid (!positive) work1)
        rintro ⟨result, after⟩ ⟨hm, hp⟩
        refine ⟨by dsimp [work1] at hm ⊢; omega, ?_⟩
        cases result with
        | Ok value => simpa [decodeFormula, Fang.QuantifiedFOF.Formula.nnf] using hp
        | Err error => cases error <;> exact hp
      | -- Every other constructor first accounts for one output node.
        apply spec_bind (allocate_spec work1 1#usize limits)
        intro answer allocated
        unfold AllocationAnswer at allocated
        split at allocated
        next fitsAllocation =>
          obtain ⟨nodes, rfl, nodes_eq⟩ := allocated
          simp only [Aeneas.Std.uncurry, bind_ok]
          let work2 : Work := {statistics := {work.statistics with operations := operation, allocated_nodes := nodes}}
          first
          | -- Both Boolean constants obey the requested polarity.
            cases positive <;>
              simp [CopyPost, work1, decodeNnf, decodeFormula, Fang.QuantifiedFOF.Formula.nnf] <;> omega
          | -- Binary constructors normalize left before right, with their exact polarities.
            have leftValid : FormulaValid signature allowed left := valid.1
            have rightValid : FormulaValid signature allowed right := valid.2
            apply spec_bind (ihl allowed leftValid _ work2)
            rintro ⟨leftResult, work3⟩ ⟨hm, hp⟩
            dsimp only at hm hp
            cases leftResult with
            | Err error =>
              cases error with
              | Invalid kind => exact False.elim hp
              | Unsupported kind => exact False.elim hp
              | Resource kind =>
                simpa [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost] using
                  (show work.statistics.operations.val ≤ work3.statistics.operations.val ∧ CopyResource kind from
                    ⟨by dsimp [work2] at hm; omega, hp⟩)
            | Ok leftNnf =>
              simp -failIfUnchanged only [Aeneas.Std.uncurry, bind_ok]
              apply spec_bind (ihr allowed rightValid positive work3)
              rintro ⟨rightResult, after⟩ ⟨hm2, hp2⟩
              dsimp only at hm2 hp2
              cases rightResult with
              | Err error =>
                cases error with
                | Invalid kind => exact False.elim hp2
                | Unsupported kind => exact False.elim hp2
                | Resource kind =>
                  simpa [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost] using
                    (show work.statistics.operations.val ≤ after.statistics.operations.val ∧ CopyResource kind from
                      ⟨by dsimp [work2] at hm; omega, hp2⟩)
              | Ok rightNnf =>
                cases positive <;>
                  simp [Aeneas.Std.uncurry, CopyPost, decodeNnf, decodeFormula,
                    Fang.QuantifiedFOF.Formula.nnf, hp, hp2] <;>
                  dsimp [work2] at hm <;> omega
          | -- Quantifier duality preserves the binder ID and normalizes its body.
            apply spec_bind (ih (fun varId => id = varId ∨ allowed varId) valid positive work2)
            rintro ⟨bodyResult, after⟩ ⟨hm, hp⟩
            dsimp only at hm hp
            cases bodyResult with
            | Err error =>
              cases error with
              | Invalid kind => exact False.elim hp
              | Unsupported kind => exact False.elim hp
              | Resource kind =>
                simpa [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost] using
                  (show work.statistics.operations.val ≤ after.statistics.operations.val ∧ CopyResource kind from
                    ⟨by dsimp [work2] at hm; omega, hp⟩)
            | Ok bodyNnf =>
              cases positive <;>
                simp [Aeneas.Std.uncurry,
                  CopyPost, decodeNnf, decodeFormula, Fang.QuantifiedFOF.Formula.nnf, hp] <;>
                dsimp [work2] at hm <;> omega
        next exceedsAllocation =>
          rw [allocated]
          simpa [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource, work1] using
            (show work.statistics.operations.val ≤ operation.val by omega)
    next exceedsOperations =>
      rw [ticked]
      simp [Aeneas.Std.uncurry, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, CopyPost, CopyResource]

end FangSkolemEmbeddedCore
