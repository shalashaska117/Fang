/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed tasks as the extracted Skolem entry receives them. The width transport and the preprocessing theorems are the accepted ones; nothing is re-modelled. -/
import NumericTask
import ExpandedBounds
import OriginalInput

open Aeneas Aeneas.Std

namespace Fang.TptpCandidate.Roles.Numeric
open FullFof

/-- FOF items with their signs, in task order. -/
def signedFormulas : List SignedNumeric → List (Bool × QuantifiedFOF.Formula)
  | [] => []
  | .cnf _ :: rest => signedFormulas rest
  | .fof positive formula :: rest => (positive, formula) :: signedFormulas rest

/-- CNF items, in task order. They do not pass through the Skolem entry. -/
def retainedClauses : List SignedNumeric → Fang.Problem
  | [] => []
  | .cnf clause :: rest => clause :: retainedClauses rest
  | .fof _ _ :: rest => retainedClauses rest

/-- Each FOF item goes through the accepted checked width transport with its own sign. -/
def encodeSigned : List (Bool × QuantifiedFOF.Formula) →
    Except FangOriginalInput.Error (List fang_skolem_core.Declaration)
  | [] => .ok []
  | (positive, formula) :: rest => do
    let declaration ← FangOriginalInput.liftWidth
      (FangQuantifiedTransport.encodeDeclaration positive formula)
    pure (declaration :: (← encodeSigned rest))

structure SignedPrepared where
  declarations : Slice fang_skolem_core.Declaration
  signature : fang_skolem_core.fang_quantified_fof_core.Signature

/-- Complete original function arities. Predicate arities are the complete original table followed by the reserved binary equality slot. -/
def prepareTask (input : SignedInput) (task : List SignedNumeric) :
    Except FangOriginalInput.Error SignedPrepared := do
  let signature ← FangOriginalInput.liftWidth (FangQuantifiedTransport.encodeSignature
    (input.functions.map Prod.snd) (input.predicates.map Prod.snd ++ [2]))
  let declarations ← encodeSigned (signedFormulas task)
  let declarations ← FangOriginalInput.checkedSlice declarations
  pure ⟨declarations, signature⟩

def EncodesSigned (source : Bool × QuantifiedFOF.Formula) (target : fang_skolem_core.Declaration) :
    Prop :=
  target.positive = source.1 ∧ FangSkolemEmbeddedCore.decodeFormula target.formula = source.2

theorem encodeSigned_related {source target} (success : encodeSigned source = .ok target) :
    List.Forall₂ EncodesSigned source target := by
  induction source generalizing target with
  | nil => cases Except.ok.inj success; exact .nil
  | cons item rest ih =>
    obtain ⟨positive, formula⟩ := item
    obtain ⟨declaration, declarationRun, success⟩ := FangOriginalInput.bind_success success
    obtain ⟨tail, tailRun, success⟩ := FangOriginalInput.bind_success success
    cases Except.ok.inj success
    exact .cons (FangQuantifiedTransport.encodeDeclaration_decode
      (FangOriginalInput.liftWidth_success declarationRun)) (ih tailRun)

/-- The exact sign and decoded formula of every declaration, in order. -/
theorem related_view {source target} (relation : List.Forall₂ EncodesSigned source target) :
    target.map (fun declaration =>
      (declaration.positive, FangSkolemEmbeddedCore.decodeFormula declaration.formula)) = source := by
  induction relation with
  | nil => rfl
  | cons head _ ih =>
    simp only [EncodesSigned] at head
    rw [List.map_cons, ih, head.1, head.2]

theorem signed_hold {source target} (relation : List.Forall₂ EncodesSigned source target)
    {D : Type} (model : Fang.Interpretation D) :
    FangQuantifiedPipeline.SignedDeclarationsHold model target ↔
      ∀ item ∈ source, ∀ valuation, GroundFOF.signed item.1 (item.2.Holds model valuation) := by
  induction relation with
  | nil => simp [FangQuantifiedPipeline.SignedDeclarationsHold]
  | cons head tail ih =>
    simp only [FangQuantifiedPipeline.SignedDeclarationsHold, List.forall_mem_cons] at ih ⊢
    simp only [EncodesSigned] at head
    rw [head.1, head.2]
    exact and_congr Iff.rfl ih

theorem prepareTask_runs {input task prepared} (success : prepareTask input task = .ok prepared) :
    FangQuantifiedTransport.encodeSignature (input.functions.map Prod.snd)
        (input.predicates.map Prod.snd ++ [2]) = .ok prepared.signature ∧
      ∃ declarations, encodeSigned (signedFormulas task) = .ok declarations ∧
        prepared.declarations.val = declarations := by
  obtain ⟨signature, signatureRun, success⟩ := FangOriginalInput.bind_success success
  obtain ⟨declarations, declarationsRun, success⟩ := FangOriginalInput.bind_success success
  obtain ⟨slice, sliceRun, success⟩ := FangOriginalInput.bind_success success
  cases Except.ok.inj success
  exact ⟨FangOriginalInput.liftWidth_success signatureRun, declarations, declarationsRun,
    FangOriginalInput.checkedSlice_values sliceRun⟩

/-- What the extracted entry receives: the task's signs and formulas, unchanged. -/
theorem prepareTask_view {input task prepared} (success : prepareTask input task = .ok prepared) :
    prepared.declarations.val.map (fun declaration =>
        (declaration.positive, FangSkolemEmbeddedCore.decodeFormula declaration.formula)) =
      signedFormulas task ∧
    prepared.signature.functions.val.map (fun value => value.val) = input.functions.map Prod.snd ∧
    prepared.signature.predicates.val.map (fun value => value.val) =
      input.predicates.map Prod.snd ++ [2] := by
  obtain ⟨signatureRun, declarations, declarationsRun, same⟩ := prepareTask_runs success
  rw [same]
  exact ⟨related_view (encodeSigned_related declarationsRun),
    FangQuantifiedTransport.encodeSignature_values signatureRun⟩

theorem signedFormulas_append (left right : List SignedNumeric) :
    signedFormulas (left ++ right) = signedFormulas left ++ signedFormulas right := by
  induction left with
  | nil => rfl
  | cons item rest ih => cases item <;> simp [signedFormulas, ih]

theorem mem_signedFormulas {task : List SignedNumeric} {positive formula}
    (member : (positive, formula) ∈ signedFormulas task) : SignedNumeric.fof positive formula ∈ task := by
  induction task with
  | nil => cases member
  | cons item rest ih =>
    cases item with
    | cnf clause => exact List.mem_cons_of_mem _ (ih member)
    | fof sign other =>
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih member)

theorem selectBlock_signs_positive {select rows item}
    (member : item ∈ signedFormulas (selectBlock select rows)) : item.1 = true := by
  obtain ⟨sign, formula⟩ := item
  obtain ⟨_, _, _, declaration, _, same⟩ := selectBlock_member (mem_signedFormulas member)
  cases declaration with
  | cnf clause => cases same
  | fof other => cases same; rfl

/-- For one original goal the entry receives, in source order, the premise FOF formulas with the positive sign and the goal's own encoded formula, built with its original variable map, as the only negative declaration. -/
theorem goalTask_entry {values input before goal after items prepared}
    (success : readSigned values = some input) (closed : Bytes.Closed values)
    (split : input.rows = before ++ goal :: after) (task : goalTask before goal after = some items)
    (encoded : prepareTask input items = .ok prepared) :
    ∃ original, goal.row.original.body = .fof original ∧
      prepared.declarations.val.map (fun declaration =>
          (declaration.positive, FangSkolemEmbeddedCore.decodeFormula declaration.formula)) =
        signedFormulas (selectBlock isPremise before) ++
          (false, original.encode input.functions input.predicates original.variables) ::
            signedFormulas (selectBlock isPremise after) ∧
      ∀ item ∈ signedFormulas (selectBlock isPremise before) ++ signedFormulas (selectBlock isPremise after),
        item.1 = true := by
  obtain ⟨_, formula, shape, rfl⟩ := goalTask_shape task
  have goalMember : goal ∈ input.rows := by rw [split]; simp
  obtain ⟨body, _, _⟩ := readSigned_row success closed goalMember
  rw [shape] at body
  obtain ⟨original, originalShape, rfl⟩ := readBody_fof body
  refine ⟨original, originalShape, ?_, ?_⟩
  · rw [(prepareTask_view encoded).1, signedFormulas_append]
    rfl
  · intro item member
    rcases List.mem_append.mp member with inBefore | inAfter
    · exact selectBlock_signs_positive inBefore
    · exact selectBlock_signs_positive inAfter

theorem taskModels_parts {D : Type} {model : Fang.Interpretation D} :
    ∀ {task : List SignedNumeric}, TaskModels model task →
      (retainedClauses task).Models model ∧
        ∀ item ∈ signedFormulas task, ∀ valuation, GroundFOF.signed item.1 (item.2.Holds model valuation)
  | [], _ => by simp [retainedClauses, signedFormulas, Fang.Problem.Models]
  | item :: rest, holds => by
    have tail := taskModels_parts (task := rest)
      (fun other member => holds other (List.mem_cons_of_mem _ member))
    have head := holds item List.mem_cons_self
    cases item with
    | cnf clause =>
      simp only [retainedClauses, signedFormulas, Fang.Problem.Models, List.forall_mem_cons] at tail ⊢
      exact ⟨⟨head, tail.1⟩, tail.2⟩
    | fof positive formula =>
      simp only [retainedClauses, signedFormulas, List.forall_mem_cons] at tail ⊢
      exact ⟨tail.1, head.2, tail.2⟩

theorem mem_retainedClauses {task : List SignedNumeric} {clause}
    (member : clause ∈ retainedClauses task) : SignedNumeric.cnf clause ∈ task := by
  induction task with
  | nil => cases member
  | cons item rest ih =>
    cases item with
    | fof sign formula => exact List.mem_cons_of_mem _ (ih member)
    | cnf other =>
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih member)

/-- Every CNF item of a task is a CNF block entry of an original row. -/
def FromRows (input : SignedInput) (task : List SignedNumeric) : Prop :=
  ∀ clause, SignedNumeric.cnf clause ∈ task →
    ∃ row ∈ input.rows, NamedQuantified.NumericDeclaration.cnf clause ∈ row.row.declarations

theorem selectBlock_fromRows {select rows clause}
    (member : SignedNumeric.cnf clause ∈ selectBlock select rows) :
    ∃ row ∈ rows, NamedQuantified.NumericDeclaration.cnf clause ∈ row.row.declarations := by
  obtain ⟨row, rowMember, _, declaration, present, same⟩ := selectBlock_member member
  cases declaration with
  | cnf other =>
    cases same
    exact ⟨row, rowMember, present⟩
  | fof formula => cases same

theorem goalTask_fromRows {input before goal after items}
    (split : input.rows = before ++ goal :: after) (task : goalTask before goal after = some items) :
    FromRows input items := by
  obtain ⟨_, formula, _, rfl⟩ := goalTask_shape task
  intro clause member
  rcases List.mem_append.mp member with inBefore | rest
  · obtain ⟨row, present, inside⟩ := selectBlock_fromRows inBefore
    exact ⟨row, by rw [split]; simp [present], inside⟩
  · rcases List.mem_cons.mp rest with same | inAfter
    · cases same
    · obtain ⟨row, present, inside⟩ := selectBlock_fromRows inAfter
      exact ⟨row, by rw [split]; simp [present], inside⟩

theorem inputsTask_fromRows (input : SignedInput) : FromRows input (inputsTask input) :=
  fun _ member => selectBlock_fromRows member

/-- Retained CNF stays within the original function range required by the accepted Skolem composition. -/
theorem retained_below {values input task} (success : readSigned values = some input)
    (fromRows : FromRows input task) :
    FangQuantifiedPipeline.ProblemBelow input.functions.length (retainedClauses task) := by
  obtain ⟨read, _, _, _⟩ := readSigned_exact success
  intro clause member
  obtain ⟨row, rowMember, present⟩ := fromRows clause (mem_retainedClauses member)
  exact Integration.readInput_below read (.cnf clause)
    (List.mem_flatMap.mpr ⟨row.row, List.mem_map_of_mem rowMember, present⟩)

theorem prepareTask_function_count {input task prepared}
    (success : prepareTask input task = .ok prepared) :
    prepared.signature.functions.val.length = input.functions.length := by
  have values := (prepareTask_view success).2.1
  simpa only [List.length_map] using congrArg List.length values

/-- A refutation after the actual Skolem call and actual per-block removal and clausification excludes every model of the signed task. -/
theorem prepareTask_unsat {values input task prepared limits output blocks}
    (success : readSigned values = some input)
    (encoded : prepareTask input task = .ok prepared)
    (skolem : fang_skolem_core.skolemize_problem prepared.declarations prepared.signature limits =
      .ok (.Ok output))
    (steps : List.Forall₂ FangQuantifiedPipeline.ActualClausificationStep output.formulas.val blocks)
    (fromRows : FromRows input task)
    (refutation : ¬ Fang.Satisfiable (retainedClauses task ++ blocks.flatten)) :
    ¬ TaskSatisfiable input task := by
  rintro ⟨D, inhabited, model, holds⟩
  obtain ⟨retainedHold, signedHold⟩ := taskModels_parts holds
  obtain ⟨_, declarations, declarationsRun, same⟩ := prepareTask_runs encoded
  have reserved : FangQuantifiedPipeline.ProblemBelow prepared.signature.functions.val.length
      (retainedClauses task) := by
    rw [prepareTask_function_count encoded]
    exact retained_below success fromRows
  apply FangQuantifiedPipeline.skolem_actual_problem_unsat skolem (retainedClauses task) reserved
    blocks steps refutation
  refine ⟨D, inhabited, FullFof.reserve input.predicates.length model, retainedHold, ?_⟩
  rw [same]
  exact (signed_hold (encodeSigned_related declarationsRun) _).mpr signedHold

/-- One original goal: the actual signed preprocessing call and a refutation of its output prove the RoleModels entailment of that goal. -/
theorem goalTask_skolem_entails {values input before goal after items prepared limits output blocks}
    (success : readSigned values = some input) (closed : Bytes.Closed values)
    (split : input.rows = before ++ goal :: after) (task : goalTask before goal after = some items)
    (encoded : prepareTask input items = .ok prepared)
    (skolem : fang_skolem_core.skolemize_problem prepared.declarations prepared.signature limits =
      .ok (.Ok output))
    (steps : List.Forall₂ FangQuantifiedPipeline.ActualClausificationStep output.formulas.val blocks)
    (refutation : ¬ Fang.Satisfiable (retainedClauses items ++ blocks.flatten)) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
        Bytes.sentence model goal.declaration.original :=
  goalTask_refuted_entails success closed split task
    (prepareTask_unsat success encoded skolem steps (goalTask_fromRows split task) refutation)

/-- Every original goal needs its own refuted signed call; together they prove original-byte entailment of every original conjecture. -/
theorem tasks_skolem_entails {bytes maximum values input}
    (decoded : Bytes.decodeBytes bytes maximum = .ok values) (success : readSigned values = some input)
    (refuted : ∀ split ∈ splits input.rows, split.2.1.role = .conjecture →
      ∃ items prepared limits output blocks,
        goalTask split.1 split.2.1 split.2.2 = some items ∧ prepareTask input items = .ok prepared ∧
        fang_skolem_core.skolemize_problem prepared.declarations prepared.signature limits =
          .ok (.Ok output) ∧
        List.Forall₂ FangQuantifiedPipeline.ActualClausificationStep output.formulas.val blocks ∧
        ¬ Fang.Satisfiable (retainedClauses items ++ blocks.flatten)) :
    Bytes.BytesEntailsAll bytes maximum := by
  apply tasks_refuted_entails decoded success
  rintro ⟨before, goal, after⟩ member role
  obtain ⟨items, prepared, limits, output, blocks, task, encoded, skolem, steps, refutation⟩ :=
    refuted (before, goal, after) member role
  exact ⟨items, task, prepareTask_unsat success encoded skolem steps
    (goalTask_fromRows (mem_splits.mp member) task) refutation⟩

/-- Without an original goal, a refutation shows only that the positive inputs are unsatisfiable. -/
theorem inputs_skolem_unsat {bytes maximum values input prepared limits output blocks}
    (decoded : Bytes.decodeBytes bytes maximum = .ok values) (success : readSigned values = some input)
    (noGoals : Roles.goals (Bytes.source values) = [])
    (encoded : prepareTask input (inputsTask input) = .ok prepared)
    (skolem : fang_skolem_core.skolemize_problem prepared.declarations prepared.signature limits =
      .ok (.Ok output))
    (steps : List.Forall₂ FangQuantifiedPipeline.ActualClausificationStep output.formulas.val blocks)
    (refutation : ¬ Fang.Satisfiable (retainedClauses (inputsTask input) ++ blocks.flatten)) :
    ¬ Bytes.BytesInputsSatisfiable bytes maximum := by
  rw [← inputsTask_satisfiable_iff decoded success noGoals]
  exact prepareTask_unsat success encoded skolem steps (inputsTask_fromRows input) refutation

#print axioms Fang.TptpCandidate.Roles.Numeric.encodeSigned_related
#print axioms Fang.TptpCandidate.Roles.Numeric.related_view
#print axioms Fang.TptpCandidate.Roles.Numeric.signed_hold
#print axioms Fang.TptpCandidate.Roles.Numeric.prepareTask_runs
#print axioms Fang.TptpCandidate.Roles.Numeric.prepareTask_view
#print axioms Fang.TptpCandidate.Roles.Numeric.signedFormulas_append
#print axioms Fang.TptpCandidate.Roles.Numeric.mem_signedFormulas
#print axioms Fang.TptpCandidate.Roles.Numeric.selectBlock_signs_positive
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_entry
#print axioms Fang.TptpCandidate.Roles.Numeric.taskModels_parts
#print axioms Fang.TptpCandidate.Roles.Numeric.mem_retainedClauses
#print axioms Fang.TptpCandidate.Roles.Numeric.selectBlock_fromRows
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_fromRows
#print axioms Fang.TptpCandidate.Roles.Numeric.inputsTask_fromRows
#print axioms Fang.TptpCandidate.Roles.Numeric.retained_below
#print axioms Fang.TptpCandidate.Roles.Numeric.prepareTask_function_count
#print axioms Fang.TptpCandidate.Roles.Numeric.prepareTask_unsat
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_skolem_entails
#print axioms Fang.TptpCandidate.Roles.Numeric.tasks_skolem_entails
#print axioms Fang.TptpCandidate.Roles.Numeric.inputs_skolem_unsat

end Fang.TptpCandidate.Roles.Numeric
