/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ScopedClausify

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace FangScopedFof
open fang_fof_core

def NnfEntryPost (formula : Nnf) (signature : Signature) (scope : VariableScope)
    (before : Statistics) (answer : core.result.Result Preprocessed fang_fof_core.Error) : Prop :=
  match answer with
  | .Ok output =>
      before.operations.val ≤ output.statistics.operations.val ∧
      (∀ clause ∈ output.clauses.val, ∀ literal ∈ clause.val, LiteralScoped signature scope literal) ∧
      decodeClauses output.clauses.val = (decodeNnf formula).clauses ∧
      output.statistics.output_clauses.val = output.clauses.val.length
  | .Err (.Invalid _) => False
  | .Err (.Resource kind) => CnfResource kind

/-- Totality in the generated Result model assumes the scoped term invariant.
    The successful clause list is exact, including order and duplicates. -/
theorem clausify_nnf_from_spec (formula : Nnf) (signature : Signature)
    (scope : VariableScope) (valid : NnfScoped signature scope formula)
    (limits : Limits) (before : Statistics) :
    nnf_entry.clausify_nnf_from formula limits before ⦃ NnfEntryPost formula signature scope before ⦄ := by
  unfold nnf_entry.clausify_nnf_from
  apply spec_bind (bounded_add_spec before.operations 0#usize limits.max_operations .Operations)
  intro result checked
  unfold BoundedAnswer at checked
  split at checked
  next fits =>
    obtain ⟨value, rfl, value_eq⟩ := checked
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    apply spec_bind (bounded_add_spec before.allocated_nodes 0#usize limits.max_stored_nodes .StoredNodes)
    intro result checked
    unfold BoundedAnswer at checked
    split at checked
    next fitsStorage =>
      obtain ⟨nodes, rfl, nodes_eq⟩ := checked
      simp only [bind_ok]
      apply spec_bind (clausify_nnf_spec formula valid limits {statistics := before})
      rintro ⟨answer, after⟩ ⟨monotone, clausified⟩
      dsimp only at monotone clausified
      simp only [Aeneas.Std.uncurry]
      cases answer with
      | Err error =>
        cases error with
        | Invalid invalid => exact False.elim clausified
        | Resource kind =>
          simpa [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            NnfEntryPost, CnfChecked] using clausified
      | Ok cnf =>
        simp only [bind_ok, spec_ok, NnfEntryPost]
        exact ⟨monotone, clausified.1.1, clausified.2, by simp⟩
    next exceedsStorage =>
      rw [checked]
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        NnfEntryPost, CnfResource, CopyResource]
  next exceeds =>
    rw [checked]
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      NnfEntryPost, CnfResource, CopyResource]

theorem clausify_nnf_from_success (formula : Nnf) (signature : Signature)
    (scope : VariableScope) (valid : NnfScoped signature scope formula)
    (limits : Limits) (before : Statistics) (output : Preprocessed)
    (success : nnf_entry.clausify_nnf_from formula limits before = .ok (.Ok output)) :
    NnfEntryPost formula signature scope before (.Ok output) := by
  have checked := clausify_nnf_from_spec formula signature scope valid limits before
  simpa [success] using checked

theorem clausify_nnf_from_semantics (formula : Nnf) (signature : Signature)
    (scope : VariableScope) (valid : NnfScoped signature scope formula)
    (limits : Limits) (before : Statistics) (output : Preprocessed)
    (success : nnf_entry.clausify_nnf_from formula limits before = .ok (.Ok output))
    {D : Type} (model : Fang.Interpretation D) (valuation : Nat → D) :
    Fang.GroundFOF.HoldsAt model valuation (decodeClauses output.clauses.val) ↔
      (decodeNnf formula).Holds model valuation := by
  have checked := clausify_nnf_from_success formula signature scope valid limits before output success
  rw [checked.2.2.1]
  exact Fang.GroundFOF.clauses_holdsAt model valuation (decodeNnf formula)

theorem clausify_nnf_from_models (formula : Nnf) (signature : Signature)
    (scope : VariableScope) (valid : NnfScoped signature scope formula)
    (limits : Limits) (before : Statistics) (output : Preprocessed)
    (success : nnf_entry.clausify_nnf_from formula limits before = .ok (.Ok output))
    {D : Type} (model : Fang.Interpretation D) :
    (decodeClauses output.clauses.val).Models model ↔
      ∀ valuation, (decodeNnf formula).Holds model valuation := by
  rw [Fang.GroundFOF.models_iff_holdsAt]
  exact forall_congr' (fun valuation =>
    clausify_nnf_from_semantics formula signature scope valid limits before output success model valuation)

end FangScopedFof
