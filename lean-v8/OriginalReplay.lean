/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent checker glue around the actual extracted preprocessing functions.
   No Rust preprocessing algorithm is reimplemented here. -/
import OriginalInput

open Aeneas Aeneas.Std

namespace FangOriginalReplay
open Fang.QuantifiedCertificate FangQuantifiedPipeline

inductive Error where
  | input : String → Error
  | encoding : FangOriginalInput.Error → Error
  | skolem : fang_skolem_core.Error → Error
  | removal : fang_binder_removal_core.Error → Error
  | clausification : fang_fof_core.Error → Error
  | runtimeEffect
  | divergence
  | clauseBlockCount

/-- Checker stage limits. Removal/clausification limits apply to each FOF block;
    a separate process guard must bound the complete native checker execution.
    This is not a proof of the Rust wrapper's cumulative resource accounting. -/
structure Limits where
  skolem : fang_skolem_core.Limits
  removal : fang_binder_removal_core.Limits
  clausification : fang_fof_core.Limits

def observe {α ε : Type} (action : Result (core.result.Result α ε))
    (rejected : ε → Error) : Except Error α :=
  match action.match with
  | .ok (.Ok value) => .ok value
  | .ok (.Err error) => .error (rejected error)
  | .vis _ _ => .error .runtimeEffect
  | .div => .error .divergence

def initialStatistics : fang_fof_core.Statistics :=
  ⟨0#usize, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize, 0#usize⟩

def replayBlocks (limits : Limits) : List fang_skolem_core.fang_quantified_fof_core.Nnf →
    Except Error (List Fang.Problem)
  | [] => .ok []
  | formula :: rest => do
    let removed ← observe (fang_binder_removal_core.remove_universals
      (skolemNnf formula) limits.removal) .removal
    let clauses ← observe (fang_fof_core.nnf_entry.clausify_nnf_from
      (removedNnf removed.formula) limits.clausification initialStatistics) .clausification
    pure (FangScopedFof.decodeClauses clauses.clauses.val :: (← replayBlocks limits rest))

def assemble : List Fang.NamedQuantified.NumericDeclaration → List Fang.Problem → Except Error Fang.Problem
  | [], [] => .ok []
  | [], _ :: _ => .error .clauseBlockCount
  | .cnf clause :: rest, blocks => do pure (Fang.dedup clause :: (← assemble rest blocks))
  | .fof _ :: _, [] => .error .clauseBlockCount
  | .fof _ :: rest, block :: blocks => do pure (Fang.preprocess block ++ (← assemble rest blocks))

def prepare (input : String) (limits : Limits) : Except Error Fang.DecodedProblem := do
  let decoded ← (Fang.QuantifiedFrontend.decode input).mapError .input
  let encoded ← (FangOriginalInput.encodeInput decoded).mapError .encoding
  let transformed ← observe (fang_skolem_core.skolemize_problem
    encoded.declarations encoded.signature limits.skolem) .skolem
  let blocks ← replayBlocks limits transformed.formulas.val
  let problem ← assemble decoded.declarations blocks
  pure {
    problem
    functionArities := transformed.signature.functions.val.map (fun value => value.val)
    predicateArities := transformed.signature.predicates.val.map (fun value => value.val) }

theorem bind_success {α β : Type} {action : Except Error α} {next : α → Except Error β} {output}
    (success : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem mapError_success {α ε : Type} {action : Except ε α} {map : ε → Error} {output}
    (success : action.mapError map = .ok output) : action = .ok output := by
  cases action with
  | error error => cases success
  | ok value => cases Except.ok.inj success; rfl

theorem observe_success {α ε : Type} {action : Result (core.result.Result α ε)}
    {rejected : ε → Error} {output} (success : observe action rejected = .ok output) :
    action = .ok (.Ok output) := by
  cases observed : action.match with
  | ok result =>
    cases result with
    | Ok value =>
      have same : value = output := Except.ok.inj (by simpa only [observe, observed] using success)
      subst output
      exact Result.match.isOk.mp observed
    | Err error => simp [observe, observed] at success
  | vis effect next => simp [observe, observed] at success
  | div => simp [observe, observed] at success

theorem replayBlocks_steps {limits formulas blocks} (success : replayBlocks limits formulas = .ok blocks) :
    List.Forall₂ ActualClausificationStep formulas blocks := by
  induction formulas generalizing blocks with
  | nil => cases Except.ok.inj success; exact .nil
  | cons formula rest ih =>
    obtain ⟨removed, removalRun, success⟩ := bind_success success
    obtain ⟨output, clauseRun, success⟩ := bind_success success
    obtain ⟨tail, tailRun, success⟩ := bind_success success
    cases Except.ok.inj success
    exact .cons ⟨limits.removal, removed, limits.clausification, initialStatistics, output,
      observe_success removalRun, observe_success clauseRun, rfl⟩ (ih tailRun)

theorem assemble_layout {source blocks prepared} (success : assemble source blocks = .ok prepared) :
    MixedLayout source blocks prepared := by
  induction source generalizing blocks prepared with
  | nil =>
    cases blocks with
    | nil => cases Except.ok.inj success; exact .nil
    | cons block rest => cases success
  | cons declaration rest ih =>
    cases declaration with
    | cnf clause =>
      obtain ⟨tail, tailRun, success⟩ := bind_success success
      cases Except.ok.inj success
      exact .cnf clause (ih tailRun)
    | fof formula =>
      cases blocks with
      | nil => cases success
      | cons block restBlocks =>
        obtain ⟨tail, tailRun, success⟩ := bind_success success
        cases Except.ok.inj success
        exact .fof formula block (ih tailRun)

theorem prepare_witness {input limits prepared} (success : prepare input limits = .ok prepared) :
    ∃ decoded encoded transformed blocks,
      Fang.QuantifiedFrontend.decode input = .ok decoded ∧
      FangOriginalInput.encodeInput decoded = .ok encoded ∧
      fang_skolem_core.skolemize_problem encoded.declarations encoded.signature limits.skolem = .ok (.Ok transformed) ∧
      List.Forall₂ ActualClausificationStep transformed.formulas.val blocks ∧
      MixedLayout decoded.declarations blocks prepared.problem ∧
      prepared.functionArities = transformed.signature.functions.val.map (fun value => value.val) ∧
      prepared.predicateArities = transformed.signature.predicates.val.map (fun value => value.val) := by
  obtain ⟨decoded, decodedRun, success⟩ := bind_success success
  obtain ⟨encoded, encodedRun, success⟩ := bind_success success
  obtain ⟨transformed, transformedRun, success⟩ := bind_success success
  obtain ⟨blocks, blocksRun, success⟩ := bind_success success
  obtain ⟨problem, problemRun, success⟩ := bind_success success
  cases Except.ok.inj success
  exact ⟨decoded, encoded, transformed, blocks, mapError_success decodedRun, mapError_success encodedRun,
    observe_success transformedRun, replayBlocks_steps blocksRun, assemble_layout problemRun, rfl, rfl⟩

/-- Actual replay constructs every generated-call and layout witness. The input
    and the candidate must still be provided as the sealed bytes being checked. -/
theorem prepare_check_original_unsat {input limits prepared} (success : prepare input limits = .ok prepared)
    (certificate : Fang.Certificate) (accepted : Fang.check prepared.problem certificate = true) :
    ¬ Fang.NamedQuantified.Grammar.BytesSatisfiable (Fang.Source.Grammar.spelling input) := by
  obtain ⟨decoded, encoded, transformed, blocks, decodedRun, encodedRun, transformedRun,
    steps, layout, _, _⟩ := prepare_witness success
  exact FangOriginalInput.decode_encode_check_unsat decodedRun encodedRun transformedRun
    steps layout certificate accepted

end FangOriginalReplay
