/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import CnfBooleanProblemUnique

namespace Fang.TptpCandidate.FullFof.CnfBoolean
open Grammar


/-- Independent lexical/token productions and lexical FOF closure determine
    the source interpretation. This definition does not call the parser. -/
def BytesModels {D : Type} (input : List UInt8) (maximum : Nat)
    (model : Source.Interpretation D) : Prop :=
  ∃ values, ByteParsed input maximum values ∧ Closed values ∧ Models (source values) model

def BytesSatisfiable (input : List UInt8) (maximum : Nat := 1048576) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D), BytesModels input maximum model


theorem decode_byte_models {input maximum values}
    (success : decodeBytes input maximum = .ok values) {D : Type}
    (model : Source.Interpretation D) :
    BytesModels input maximum model ↔ Models (source values) model := by
  constructor
  · rintro ⟨other, parsed, _, models⟩
    have same := byteParsed_source_unique parsed (decode_grammar success)
    simpa only [same] using models
  · intro models
    exact ⟨values, decode_grammar success, decode_closed success, models⟩

theorem decode_bytes_satisfiable {input maximum values}
    (success : decodeBytes input maximum = .ok values) :
    BytesSatisfiable input maximum ↔ Satisfiable (source values) := by
  constructor
  · rintro ⟨domain, inhabited, model, models⟩
    exact ⟨domain, inhabited, model, (decode_byte_models success model).mp models⟩
  · rintro ⟨domain, inhabited, model, models⟩
    exact ⟨domain, inhabited, model, (decode_byte_models success model).mpr models⟩

/-- The reserved equality slot has mathematical domain equality. This is an
    original-byte model connection, not a preprocessing or certificate claim. -/
theorem decode_encoded_satisfiable {input maximum values}
    (success : decodeBytes input maximum = .ok values) :
    BytesSatisfiable input maximum ↔ EncodedSatisfiable (source values) :=
  (decode_bytes_satisfiable success).trans (encoded_satisfiable_iff values)

theorem decode_encoded_unsat {input maximum values}
    (success : decodeBytes input maximum = .ok values)
    (unsat : ¬ EncodedSatisfiable (source values)) : ¬ BytesSatisfiable input maximum :=
  fun models => unsat ((decode_encoded_satisfiable success).mp models)

end Fang.TptpCandidate.FullFof.CnfBoolean
