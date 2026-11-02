/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Whole-problem composition; caller signature/scope and byte encoding stay explicit. -/
import DeclarationMeaning
import RemovalScope

namespace FangQuantifiedPipeline

/-- Exact successful generated calls, with the input invariant still supplied
    by the caller. This relation is a proof witness, not another algorithm. -/
def ClausificationStep (formula : fang_skolem_core.fang_quantified_fof_core.Nnf)
    (clauses : Fang.Problem) : Prop :=
  ∃ (removalLimits : fang_binder_removal_core.Limits) (removed : fang_binder_removal_core.Removed)
    (signature : fang_fof_core.Signature) (scope : fang_fof_core.VariableScope)
    (limits : fang_fof_core.Limits) (before : fang_fof_core.Statistics) (output : fang_fof_core.Preprocessed),
    fang_binder_removal_core.remove_universals (skolemNnf formula) removalLimits = .ok (.Ok removed) ∧
    InputScoped signature scope (skolemNnf formula) ∧
    fang_fof_core.nnf_entry.clausify_nnf_from (removedNnf removed.formula) limits before = .ok (.Ok output) ∧
    clauses = FangScopedFof.decodeClauses output.clauses.val

theorem clausificationStep_models {formula clauses} (step : ClausificationStep formula clauses)
    (safe : Fang.QuantifiedFOF.BinderRemoval.RectifiedWithin []
      (FangSkolemCore.decodeIndependentNnf formula))
    {D : Type} [Nonempty D] (model : Fang.Interpretation D) :
    clauses.Models model ↔ ∀ valuation, (FangSkolemCore.decodeIndependentNnf formula).Holds model valuation := by
  obtain ⟨removalLimits, removed, signature, scope, limits, before, output,
    removal, valid, clausification, rfl⟩ := step
  exact remove_clausify_input_models removal [] safe signature scope valid limits before output
    clausification model

theorem models_append {D : Type} (model : Fang.Interpretation D) (left right : Fang.Problem) :
    (left ++ right).Models model ↔ left.Models model ∧ right.Models model := by
  simp only [Fang.Problem.Models, List.mem_append, or_imp, forall_and]

theorem clausificationSteps_models {formulas blocks}
    (steps : List.Forall₂ ClausificationStep formulas blocks)
    (safe : ∀ formula ∈ formulas, Fang.QuantifiedFOF.BinderRemoval.RectifiedWithin []
      (FangSkolemCore.decodeIndependentNnf formula))
    {D : Type} [Nonempty D] (model : Fang.Interpretation D) :
    Fang.Problem.Models model blocks.flatten ↔
      ∀ formula ∈ formulas, ∀ valuation, (FangSkolemCore.decodeIndependentNnf formula).Holds model valuation := by
  induction steps with
  | nil => simp [Fang.Problem.Models]
  | cons head tail ih =>
    rw [List.flatten_cons, models_append]
    simp only [List.forall_mem_cons]
    exact and_congr (clausificationStep_models head (safe _ List.mem_cons_self) model)
      (ih (fun formula member => safe formula (List.mem_cons_of_mem _ member)))

/-- Untouched CNF input also belongs to the original reserved function range. -/
def ProblemBelow (limit : Nat) (problem : Fang.Problem) : Prop :=
  ∀ clause ∈ problem, ∀ literal ∈ clause, ∀ term ∈ literal.atom.args,
    Fang.QuantifiedFOF.Skolem.TermBelow limit term

theorem literal_preserved {D : Type} {limit : Nat} {original extended : Fang.Interpretation D}
    (preserved : Fang.QuantifiedFOF.Skolem.PreservesBelow limit original extended)
    (literal : Fang.Literal)
    (below : ∀ term ∈ literal.atom.args, Fang.QuantifiedFOF.Skolem.TermBelow limit term)
    (valuation : Nat → D) :
    literal.Holds extended valuation ↔ literal.Holds original valuation := by
  have atom := Fang.QuantifiedFOF.Skolem.formula_holds_preserved preserved
    (.atom literal.atom) below valuation
  change literal.atom.Holds extended valuation ↔ literal.atom.Holds original valuation at atom
  cases positive : literal.positive <;> simp [Fang.Literal.Holds, positive, atom]

theorem problem_preserved {D : Type} {limit : Nat} {original extended : Fang.Interpretation D}
    (preserved : Fang.QuantifiedFOF.Skolem.PreservesBelow limit original extended)
    (problem : Fang.Problem) (below : ProblemBelow limit problem) :
    problem.Models extended ↔ problem.Models original := by
  apply forall_congr'
  intro clause
  apply forall_congr'
  intro member
  apply forall_congr'
  intro valuation
  apply exists_congr
  intro literal
  apply and_congr_right
  intro present
  exact literal_preserved preserved literal (below clause member literal present) valuation

def SignedDeclarationsHold {D : Type} (model : Fang.Interpretation D)
    (declarations : List fang_skolem_core.Declaration) : Prop :=
  ∀ declaration ∈ declarations, ∀ valuation, Fang.GroundFOF.signed declaration.positive
    ((FangSkolemEmbeddedCore.decodeFormula declaration.formula).Holds model valuation)

/-- One interpretation extension serves every input declaration and the retained
    CNF. The equation links generated calls to numeric semantics, not the original
    parser bytes or the native Rust wrapper's control flow. -/
theorem skolem_clausification_problem_models
    {declarations : Aeneas.Std.Slice fang_skolem_core.Declaration}
    {signature : fang_skolem_core.fang_quantified_fof_core.Signature}
    {limits : fang_skolem_core.Limits} {output : fang_skolem_core.Skolemized}
    (success : fang_skolem_core.skolemize_problem declarations signature limits = .ok (.Ok output))
    (retained : Fang.Problem) (reserved : ProblemBelow signature.functions.val.length retained)
    (blocks : List Fang.Problem) (steps : List.Forall₂ ClausificationStep output.formulas.val blocks)
    {D : Type} [Nonempty D] (original : Fang.Interpretation D) :
    ∃ extended : Fang.Interpretation D,
      Fang.QuantifiedFOF.Skolem.PreservesBelow signature.functions.val.length original extended ∧
      ((retained ++ blocks.flatten).Models extended ↔
        retained.Models original ∧ SignedDeclarationsHold original declarations.val) := by
  obtain ⟨extended, preserved, meaning⟩ := FangSkolemCore.skolemize_problem_independent_meaning success original
  refine ⟨extended, preserved, ?_⟩
  rw [models_append, problem_preserved preserved retained reserved,
    clausificationSteps_models steps (fun formula member =>
      (FangSkolemCore.skolemize_problem_output success formula member).1) extended]
  apply and_congr_right
  intro _
  constructor
  · intro target declaration member valuation
    exact (meaning valuation).mpr (fun formula present => target formula present valuation) declaration member
  · intro source formula member valuation
    exact (meaning valuation).mp (fun declaration present => source declaration present valuation) formula member

/-- A refutation of all produced clauses excludes every nonempty original model.
    Resource outcomes and saturation without refutation establish no SAT claim. -/
theorem skolem_clausification_unsat
    {declarations : Aeneas.Std.Slice fang_skolem_core.Declaration}
    {signature : fang_skolem_core.fang_quantified_fof_core.Signature}
    {limits : fang_skolem_core.Limits} {output : fang_skolem_core.Skolemized}
    (success : fang_skolem_core.skolemize_problem declarations signature limits = .ok (.Ok output))
    (retained : Fang.Problem) (reserved : ProblemBelow signature.functions.val.length retained)
    (blocks : List Fang.Problem) (steps : List.Forall₂ ClausificationStep output.formulas.val blocks)
    (refutation : ¬ Fang.Satisfiable (retained ++ blocks.flatten)) :
    ¬ ∃ (D : Type) (_ : Nonempty D) (original : Fang.Interpretation D),
      retained.Models original ∧ SignedDeclarationsHold original declarations.val := by
  rintro ⟨D, nonempty, original, cnf, fof⟩
  let : Nonempty D := nonempty
  obtain ⟨extended, _, equivalent⟩ :=
    skolem_clausification_problem_models success retained reserved blocks steps original
  exact refutation ⟨D, nonempty, extended, equivalent.mpr ⟨cnf, fof⟩⟩

end FangQuantifiedPipeline
