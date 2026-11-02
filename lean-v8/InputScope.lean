/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Derive the clausifier's variable/function invariant from actual Skolem success. -/
import DeclarationArities
import OutputIntervals
import ProblemComposition

open Aeneas.Std Aeneas.Data.ListN

namespace FangQuantifiedPipeline
open FangSkolemCore Fang.QuantifiedFOF

/-- A proof witness containing the exact returned arity tables. The Rust NNF
    entrypoint has no signature parameter and does not execute this conversion. -/
def clausifierSignature (signature : fang_skolem_core.fang_quantified_fof_core.Signature) :
    fang_fof_core.Signature := ⟨signature.functions, signature.predicates⟩

theorem mappedTerms_values {n : Nat} (terms : ListN fang_skolem_core.fang.syntax.Term n) :
    (removedTerms (skolemTerms terms)).toList =
      terms.toList.map (fun term => removedTerm (skolemTerm term)) := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp only [skolemTerms, removedTerms, ListN.toList, List.map_cons, ih]

theorem mappedVec_values (arguments : alloc.vec.Vec fang_skolem_core.fang.syntax.Term) :
    (removedVec (skolemVec arguments)).val =
      arguments.val.map (fun term => removedTerm (skolemTerm term)) := by
  cases arguments with
  | mk slice =>
    cases slice with
    | mk count terms bound =>
      simpa only [skolemVec, skolemSlice, removedVec, removedSlice, alloc.vec.Vec.val, Slice.val]
        using mappedTerms_values terms

theorem mappedTerm_valid
    (signature : fang_skolem_core.fang_quantified_fof_core.Signature) (count : U32)
    {term : fang_skolem_core.fang.syntax.Term} (arities : TermArities signature.functions term) :
    TermWithin (List.range count.val) (decodeTerm term) →
      FangScopedFof.TermValid (clausifierSignature signature) (.Bound count)
        (removedTerm (skolemTerm term)) := by
  induction arities with
  | var id =>
    intro within
    apply FangScopedFof.TermValid.var
    simpa only [decodeTerm, TermWithin, List.mem_range, FangScopedFof.VariableValid] using within
  | fun_ symbol arguments arity children ih =>
    intro within
    simp only [decodeTerm, TermWithin] at within
    change FangScopedFof.TermValid _ _ (.Fun symbol (removedVec (skolemVec arguments)))
    apply FangScopedFof.TermValid.fun_
    · simpa only [clausifierSignature, FangScopedFof.ArityMatches, FunctionArity,
        mappedVec_values, List.length_map] using arity
    · intro i inside
      have original : i < arguments.val.length := by simpa only [mappedVec_values, List.length_map] using inside
      have childWithin : TermWithin (List.range count.val) (decodeTerm arguments.val[i]) := by
        apply within
        rw [decodeVec_eq_map]
        exact List.mem_map.mpr ⟨arguments.val[i], List.getElem_mem original, rfl⟩
      simpa only [mappedVec_values, List.getElem_map] using ih i original childWithin

theorem mappedLiteral_scoped
    (signature : fang_skolem_core.fang_quantified_fof_core.Signature) (count : U32)
    (literal : fang_skolem_core.fang.syntax.Literal)
    (arities : LiteralArities signature.functions literal)
    (bounded : FlatVariables count.val (literalFormula literal)) :
    FangScopedFof.LiteralScoped (clausifierSignature signature) (.Bound count)
      (removedLiteral (skolemLiteral literal)) := by
  have within : ∀ term ∈ decodeVec literal.arguments, TermWithin (List.range count.val) term := by
    cases positive : literal.positive <;>
      simpa only [literalFormula, positive, Bool.false_eq_true, ite_false, ite_true, FlatVariables, decodeAtom]
        using bounded
  intro i inside
  have original : i < literal.arguments.val.length := by
    simpa only [removedLiteral, skolemLiteral, mappedVec_values, List.length_map] using inside
  have childWithin : TermWithin (List.range count.val) (decodeTerm literal.arguments.val[i]) := by
    apply within
    rw [decodeVec_eq_map]
    exact List.mem_map.mpr ⟨literal.arguments.val[i], List.getElem_mem original, rfl⟩
  simpa only [removedLiteral, skolemLiteral, mappedVec_values, List.getElem_map] using
    mappedTerm_valid signature count (arities i original) childWithin

theorem skolemNnf_scoped
    (signature : fang_skolem_core.fang_quantified_fof_core.Signature) (count : U32)
    (formula : fang_skolem_core.fang_quantified_fof_core.Nnf)
    (arities : NnfArities signature.functions formula)
    (bounded : FlatVariables count.val (decodeNnf formula)) :
    InputScoped (clausifierSignature signature) (.Bound count) (skolemNnf formula) := by
  induction formula with
  | Literal literal => exact mappedLiteral_scoped signature count literal arities bounded
  | True | False => trivial
  | And left right il ir | Or left right il ir => exact ⟨il arities.1 bounded.1, ir arities.2 bounded.2⟩
  | Forall id body ih | Exists id body ih => exact ih arities bounded

/-- The original rectifier count can include unused or deleted binder IDs.
    It is a mathematical witness, not a new scan or metadata field in Rust. -/
theorem skolemize_problem_scoped
    {declarations : Slice fang_skolem_core.Declaration}
    {signature : fang_skolem_core.fang_quantified_fof_core.Signature}
    {limits : fang_skolem_core.Limits} {output : fang_skolem_core.Skolemized}
    (success : fang_skolem_core.skolemize_problem declarations signature limits = .ok (.Ok output)) :
    ∀ formula ∈ output.formulas.val, ∃ count : U32,
      InputScoped (clausifierSignature output.signature) (.Bound count) (skolemNnf formula) := by
  intro formula member
  obtain ⟨count, bounded, _⟩ := skolemize_problem_intervals success formula member
  exact ⟨count, skolemNnf_scoped output.signature count formula
    ((skolemize_problem_arities success).2.1 formula member) bounded⟩

/-- Only successful generated call equations and exact ordered clause output.
    No variable-bound or function-arity premise is included. -/
def ActualClausificationStep (formula : fang_skolem_core.fang_quantified_fof_core.Nnf)
    (clauses : Fang.Problem) : Prop :=
  ∃ (removalLimits : fang_binder_removal_core.Limits) (removed : fang_binder_removal_core.Removed)
    (limits : fang_fof_core.Limits) (before : fang_fof_core.Statistics) (output : fang_fof_core.Preprocessed),
    fang_binder_removal_core.remove_universals (skolemNnf formula) removalLimits = .ok (.Ok removed) ∧
    fang_fof_core.nnf_entry.clausify_nnf_from (removedNnf removed.formula) limits before = .ok (.Ok output) ∧
    clauses = FangScopedFof.decodeClauses output.clauses.val

theorem actualStep_scoped {formula clauses}
    (signature : fang_fof_core.Signature) (scope : fang_fof_core.VariableScope)
    (valid : InputScoped signature scope (skolemNnf formula))
    (step : ActualClausificationStep formula clauses) : ClausificationStep formula clauses := by
  obtain ⟨removalLimits, removed, limits, before, output, removal, clausification, same⟩ := step
  exact ⟨removalLimits, removed, signature, scope, limits, before, output, removal, valid, clausification, same⟩

theorem actualSteps_scoped {formulas blocks}
    (signature : fang_fof_core.Signature)
    (steps : List.Forall₂ ActualClausificationStep formulas blocks)
    (valid : ∀ formula ∈ formulas, ∃ count : U32, InputScoped signature (.Bound count) (skolemNnf formula)) :
    List.Forall₂ ClausificationStep formulas blocks := by
  induction steps with
  | nil => exact .nil
  | cons head tail ih =>
    obtain ⟨count, validScope⟩ := valid _ List.mem_cons_self
    exact .cons (actualStep_scoped signature (.Bound count) validScope head)
      (ih (fun formula member => valid formula (List.mem_cons_of_mem _ member)))

/-- Actual successful preprocessing calls suffice for the per-output invariants.
    Retained original CNF still requires its original function-range bound. -/
theorem skolem_actual_problem_models
    {declarations : Slice fang_skolem_core.Declaration}
    {signature : fang_skolem_core.fang_quantified_fof_core.Signature}
    {limits : fang_skolem_core.Limits} {output : fang_skolem_core.Skolemized}
    (success : fang_skolem_core.skolemize_problem declarations signature limits = .ok (.Ok output))
    (retained : Fang.Problem) (reserved : ProblemBelow signature.functions.val.length retained)
    (blocks : List Fang.Problem) (steps : List.Forall₂ ActualClausificationStep output.formulas.val blocks)
    {D : Type} [Nonempty D] (original : Fang.Interpretation D) :
    ∃ extended : Fang.Interpretation D,
      Skolem.PreservesBelow signature.functions.val.length original extended ∧
      ((retained ++ blocks.flatten).Models extended ↔
        retained.Models original ∧ SignedDeclarationsHold original declarations.val) :=
  skolem_clausification_problem_models success retained reserved blocks
    (actualSteps_scoped (clausifierSignature output.signature) steps (skolemize_problem_scoped success)) original

theorem skolem_actual_problem_unsat
    {declarations : Slice fang_skolem_core.Declaration}
    {signature : fang_skolem_core.fang_quantified_fof_core.Signature}
    {limits : fang_skolem_core.Limits} {output : fang_skolem_core.Skolemized}
    (success : fang_skolem_core.skolemize_problem declarations signature limits = .ok (.Ok output))
    (retained : Fang.Problem) (reserved : ProblemBelow signature.functions.val.length retained)
    (blocks : List Fang.Problem) (steps : List.Forall₂ ActualClausificationStep output.formulas.val blocks)
    (refutation : ¬ Fang.Satisfiable (retained ++ blocks.flatten)) :
    ¬ ∃ (D : Type) (_ : Nonempty D) (original : Fang.Interpretation D),
      retained.Models original ∧ SignedDeclarationsHold original declarations.val :=
  skolem_clausification_unsat success retained reserved blocks
    (actualSteps_scoped (clausifierSignature output.signature) steps (skolemize_problem_scoped success)) refutation

end FangQuantifiedPipeline
