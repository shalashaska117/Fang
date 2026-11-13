/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Decoder output transport and conditional original-byte refutation composition.
   The actual extracted functions remain responsible for preprocessing. -/
import InputTransport
import MixedLayout
import RetainedBounds

open Aeneas Aeneas.Std

namespace FangOriginalInput
open Fang.NamedQuantified Fang.QuantifiedCertificate FangQuantifiedPipeline

inductive Error where
  | width : FangQuantifiedTransport.Error → Error
  | missingFunctionArity
  | missingPredicateArity
deriving DecidableEq, Repr

def liftWidth {α : Type} (action : Except FangQuantifiedTransport.Error α) : Except Error α :=
  action.mapError .width

/-- Preserve every table slot, including unused slots. Missing arities are errors. -/
def readArities (missing : Error) : List Fang.Frontend.Symbol → Except Error (List Nat)
  | [] => .ok []
  | symbol :: rest => do
    let arity ← match symbol.arity with
      | some arity => .ok arity
      | none => .error missing
    pure (arity :: (← readArities missing rest))

def checkedSlice {α : Type} (values : List α) : Except Error (Slice α) :=
  if bound : values.length ≤ Usize.max then .ok (Slice.from values bound)
  else .error (.width .vectorOverflow)

def encodeAxioms : List Fang.QuantifiedFOF.Formula → Except Error (List fang_skolem_core.Declaration)
  | [] => .ok []
  | formula :: rest => do
    let declaration ← liftWidth (FangQuantifiedTransport.encodeDeclaration true formula)
    pure (declaration :: (← encodeAxioms rest))

structure Encoded where
  declarations : Slice fang_skolem_core.Declaration
  signature : fang_skolem_core.fang_quantified_fof_core.Signature

def encodeInput (decoded : Fang.QuantifiedFrontend.Decoded) : Except Error Encoded := do
  let functions ← readArities .missingFunctionArity decoded.state.functions
  let predicates ← readArities .missingPredicateArity decoded.state.predicates
  let signature ← liftWidth (FangQuantifiedTransport.encodeSignature functions predicates)
  let declarations ← encodeAxioms (formulas decoded.declarations)
  let declarations ← checkedSlice declarations
  pure ⟨declarations, signature⟩

theorem bind_success {α β : Type} {action : Except Error α}
    {next : α → Except Error β} {output : β}
    (success : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases success
  | ok value => exact ⟨value, rfl, success⟩

theorem liftWidth_success {α : Type} {action : Except FangQuantifiedTransport.Error α} {output}
    (success : liftWidth action = .ok output) : action = .ok output := by
  cases action with
  | error error => cases success
  | ok value => cases Except.ok.inj success; rfl

theorem readArities_values {missing symbols values}
    (success : readArities missing symbols = .ok values) :
    symbols.map Fang.Frontend.Symbol.arity = values.map some := by
  induction symbols generalizing values with
  | nil => cases Except.ok.inj success; rfl
  | cons symbol rest ih =>
    cases arity : symbol.arity with
    | none => simp [readArities, arity, Bind.bind, Except.bind] at success
    | some value =>
      have run : (do pure (value :: (← readArities missing rest))) = .ok values := by
        simpa only [readArities, arity, Bind.bind, Except.bind] using success
      obtain ⟨tail, tailRun, same⟩ := bind_success run
      cases Except.ok.inj same
      simpa only [List.map_cons, arity] using congrArg (List.cons (some value)) (ih tailRun)

theorem readArities_length {missing symbols values}
    (success : readArities missing symbols = .ok values) : values.length = symbols.length := by
  simpa only [List.length_map] using (congrArg List.length (readArities_values success)).symm

theorem checkedSlice_values {α : Type} {source : List α} {target : Slice α}
    (success : checkedSlice source = .ok target) : target.val = source := by
  unfold checkedSlice at success
  split at success
  · cases Except.ok.inj success
    exact Slice.from_val _ _
  · cases success

def EncodesAxiom (formula : Fang.QuantifiedFOF.Formula) (declaration : fang_skolem_core.Declaration) : Prop :=
  declaration.positive = true ∧ FangSkolemEmbeddedCore.decodeFormula declaration.formula = formula

theorem encodeAxioms_related {source target} (success : encodeAxioms source = .ok target) :
    List.Forall₂ EncodesAxiom source target := by
  induction source generalizing target with
  | nil => cases Except.ok.inj success; exact .nil
  | cons formula rest ih =>
    obtain ⟨declaration, declarationRun, success⟩ := bind_success success
    obtain ⟨tail, tailRun, success⟩ := bind_success success
    cases Except.ok.inj success
    exact .cons (FangQuantifiedTransport.encodeDeclaration_decode (liftWidth_success declarationRun))
      (ih tailRun)

theorem encoded_axioms_hold {source target} (relation : List.Forall₂ EncodesAxiom source target)
    {D : Type} (model : Fang.Interpretation D) :
    SignedDeclarationsHold model target ↔ ∀ formula ∈ source, ∀ valuation, formula.Holds model valuation := by
  induction relation with
  | nil => simp [SignedDeclarationsHold]
  | cons head tail ih =>
    simp only [SignedDeclarationsHold, List.forall_mem_cons] at ih ⊢
    simp only [EncodesAxiom] at head
    rw [head.1, head.2]
    simpa only [Fang.GroundFOF.signed, Bool.true_eq, ite_true] using and_congr Iff.rfl ih

theorem encodeInput_runs {decoded encoded} (success : encodeInput decoded = .ok encoded) :
    ∃ functions predicates declarations,
      readArities .missingFunctionArity decoded.state.functions = .ok functions ∧
      readArities .missingPredicateArity decoded.state.predicates = .ok predicates ∧
      FangQuantifiedTransport.encodeSignature functions predicates = .ok encoded.signature ∧
      encodeAxioms (formulas decoded.declarations) = .ok declarations ∧
      encoded.declarations.val = declarations := by
  obtain ⟨functions, functionsRun, success⟩ := bind_success success
  obtain ⟨predicates, predicatesRun, success⟩ := bind_success success
  obtain ⟨signature, signatureRun, success⟩ := bind_success success
  obtain ⟨declarations, declarationsRun, success⟩ := bind_success success
  obtain ⟨slice, sliceRun, success⟩ := bind_success success
  cases Except.ok.inj success
  exact ⟨functions, predicates, declarations, functionsRun, predicatesRun,
    liftWidth_success signatureRun, declarationsRun, checkedSlice_values sliceRun⟩

theorem encodeInput_function_count {decoded encoded} (success : encodeInput decoded = .ok encoded) :
    encoded.signature.functions.val.length = decoded.state.functions.length := by
  obtain ⟨functions, predicates, declarations, functionsRun, _, signatureRun, _, _⟩ := encodeInput_runs success
  have values := (FangQuantifiedTransport.encodeSignature_values signatureRun).1
  have length : encoded.signature.functions.val.length = functions.length := by
    simpa only [List.length_map] using congrArg List.length values
  exact length.trans (readArities_length functionsRun)

theorem numeric_models_parts {source : List NumericDeclaration} {D : Type}
    (model : Fang.Interpretation D) (holds : NumericModels model source) :
    (retained source).Models model ∧ ∀ formula ∈ formulas source, ∀ valuation, formula.Holds model valuation := by
  induction source with
  | nil => simp [retained, formulas, Fang.Problem.Models]
  | cons declaration rest ih =>
    have tail := ih (fun item member => holds item (List.mem_cons_of_mem _ member))
    have head := holds declaration List.mem_cons_self
    cases declaration with
    | cnf clause =>
      refine ⟨?_, tail.2⟩
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact tail.1 item member
    | fof formula =>
      refine ⟨tail.1, ?_⟩
      intro item member valuation
      rcases List.mem_cons.mp member with rfl | member
      · exact head.2 valuation
      · exact tail.2 item member valuation

theorem encodeInput_models {decoded encoded} (success : encodeInput decoded = .ok encoded)
    {D : Type} (model : Fang.Interpretation D) (holds : NumericModels model decoded.declarations) :
    (retained decoded.declarations).Models model ∧ SignedDeclarationsHold model encoded.declarations.val := by
  obtain ⟨functions, predicates, declarations, _, _, _, declarationsRun, same⟩ := encodeInput_runs success
  obtain ⟨retainedHold, axiomsHold⟩ := numeric_models_parts model holds
  refine ⟨retainedHold, ?_⟩
  rw [same]
  exact (encoded_axioms_hold (encodeAxioms_related declarationsRun) model).mpr axiomsHold

theorem encodeInput_reserved {input decoded encoded}
    (decodedRun : Fang.QuantifiedFrontend.decode input = .ok decoded)
    (encodedRun : encodeInput decoded = .ok encoded) :
    ProblemBelow encoded.signature.functions.val.length (retained decoded.declarations) := by
  rw [encodeInput_function_count encodedRun]
  exact decode_retained_functions_below decodedRun

/-- This connects the original bytes to the actual checker under exact successful
    generated preprocessing calls and the indexed mixed-layout witness. The next
    executable replay adapter must construct those witnesses itself. -/
theorem decode_encode_check_unsat {input decoded encoded limits output blocks prepared}
    (decodedRun : Fang.QuantifiedFrontend.decode input = .ok decoded)
    (encodedRun : encodeInput decoded = .ok encoded)
    (skolemRun : fang_skolem_core.skolemize_problem encoded.declarations encoded.signature limits = .ok (.Ok output))
    (steps : List.Forall₂ ActualClausificationStep output.formulas.val blocks)
    (layout : MixedLayout decoded.declarations blocks prepared)
    (certificate : Fang.Certificate) (accepted : Fang.check prepared certificate = true) :
    ¬ Fang.NamedQuantified.Grammar.BytesSatisfiable (Fang.Source.Grammar.spelling input) := by
  apply Fang.QuantifiedFrontend.decode_bytes_unsat decodedRun
  rintro ⟨D, inhabited, model, holds⟩
  have refuted := skolem_actual_problem_unsat skolemRun (retained decoded.declarations)
    (encodeInput_reserved decodedRun encodedRun) blocks steps (mixedLayout_check_unsat layout certificate accepted)
  exact refuted ⟨D, inhabited, model, encodeInput_models encodedRun model holds⟩

end FangOriginalInput
