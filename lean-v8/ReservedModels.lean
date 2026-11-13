/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ReservedInput

namespace FangQuantifiedEqualityInput
open Fang.QuantifiedEqualityFrontend Fang.QuantifiedCertificate FangQuantifiedPipeline

theorem numeric_declaration_count (source : List Encoding.EncodedDeclaration) :
    (numericDeclarations source).length = source.length := by simp [numericDeclarations]

/-- The same ordered declaration list supplies both retained CNF and FOF bodies.
    Names are metadata and do not change their model conditions. -/
theorem encoded_models_parts {source : List Encoding.EncodedDeclaration} {D : Type}
    (model : Fang.Interpretation D) :
    Encoding.Models model source ↔
      (retained (numericDeclarations source)).Models model ∧
      ∀ formula ∈ formulas (numericDeclarations source), ∀ valuation, formula.Holds model valuation := by
  induction source with
  | nil => simp [Encoding.Models, numericDeclarations, retained, formulas, Fang.Problem.Models]
  | cons declaration rest ih =>
    cases declaration with
    | cnf sourceName clause =>
      simpa only [Encoding.Models, Encoding.EncodedDeclaration.Valid, numericDeclarations, List.map_cons,
        numericDeclaration, retained, formulas, List.forall_mem_cons, Fang.Problem.Models, and_assoc]
        using and_congr Iff.rfl ih
    | fof sourceName formula =>
      simpa only [Encoding.Models, Encoding.EncodedDeclaration.Valid, numericDeclarations, List.map_cons,
        numericDeclaration, retained, formulas, List.forall_mem_cons, Fang.Problem.Models]
        using (and_congr (Iff.rfl : (∀ valuation, formula.Holds model valuation) ↔
          (∀ valuation, formula.Holds model valuation)) ih).trans and_left_comm

theorem transport_models {source maximum prepared}
    (success : transport source maximum = .ok prepared) {D : Type} (model : Fang.Interpretation D) :
    Encoding.Models model source.declarations ↔
      (retained (numericDeclarations source.declarations)).Models model ∧
      SignedDeclarationsHold model prepared.declarations.val := by
  obtain ⟨_, _, declarations, _, _, _, _, declarationsRun, exactDeclarations⟩ := transport_runs success
  rw [exactDeclarations]
  exact (encoded_models_parts (source := source.declarations) model).trans
    (and_congr Iff.rfl (FangOriginalInput.encoded_axioms_hold
      (FangOriginalInput.encodeAxioms_related declarationsRun) model).symm)

end FangQuantifiedEqualityInput
