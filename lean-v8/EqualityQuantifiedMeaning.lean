/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Mixed declaration models pass through the actual reserved-equality encoding.
   Preprocessing, certificates and byte parsing are separate boundaries. -/
import EqualityQuantifiedEncodingProof

namespace Fang.NamedQuantifiedEquality

def Declaration.Valid {D : Type} (model : Source.Interpretation D) : Declaration → Prop
  | .cnf clause => clause.Valid model
  | .fof _ formula => ∀ valuation, formula.Holds model valuation

def Models {D : Type} (model : Source.Interpretation D) (declarations : List Declaration) : Prop :=
  ∀ declaration ∈ declarations, declaration.Valid model

def Satisfiable (declarations : List Declaration) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D), Models model declarations

end Fang.NamedQuantifiedEquality

namespace Fang.QuantifiedEqualityFrontend.Encoding

def EncodedDeclaration.Valid {D : Type} (model : Fang.Interpretation D) : EncodedDeclaration → Prop
  | .cnf _ clause => clause.Valid model
  | .fof _ formula => ∀ valuation, formula.Holds model valuation

def Models {D : Type} (model : Fang.Interpretation D) (declarations : List EncodedDeclaration) : Prop :=
  ∀ declaration ∈ declarations, declaration.Valid model

/-- The predicate at the reserved ID denotes domain equality on evaluated
    arguments. Arbitrary interpretations of that predicate are excluded. -/
def ReservedSatisfiable (reserved : Nat) (declarations : List EncodedDeclaration) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Fang.Interpretation D),
    Models (EqualityBridge.reserveInterpretation reserved model) declarations

theorem LiteralEncoding.holds_toNumeric {reserved signature symbols variables named encoded}
    (encoding : LiteralEncoding reserved signature symbols variables named encoded)
    {D : Type} (model : Source.Interpretation D) (valuation : Nat → D) :
    encoded.Holds (EqualityBridge.reserveInterpretation reserved (model.toNumeric symbols)) valuation ↔
      named.Holds model (fun name => valuation (variables.id name)) := by
  have atom := encoding.atom.holds (NamedQuantified.InterpretationsAgree.toNumeric symbols model)
    (fun _ _ => rfl : NamedQuantified.ValuationsAgree variables
      (fun name => valuation (variables.id name)) valuation)
  have same : (sourceAtom named.atom).Holds model (fun name => valuation (variables.id name)) =
      named.atom.Holds model (fun name => valuation (variables.id name)) := by
    cases named.atom <;> rfl
  rw [same] at atom
  simp only [Fang.Literal.Holds, EqualitySource.Literal.Holds, encoding.polarity]
  cases encoded.positive with
  | false => exact not_congr atom
  | true => exact atom

theorem DeclarationEncoding.valid_toNumeric {reserved signature symbols named encoded}
    (encoding : DeclarationEncoding reserved signature symbols named encoded)
    {D : Type} (model : Source.Interpretation D) (valid : named.Valid model) :
    encoded.Valid (EqualityBridge.reserveInterpretation reserved (model.toNumeric symbols)) := by
  cases encoding with
  | cnf variables literals =>
    intro valuation
    obtain ⟨literal, member, holds⟩ := valid (fun name => valuation (variables.id name))
    obtain ⟨output, outputMember, relation⟩ := literals.member_left member
    exact ⟨output, outputMember, (relation.holds_toNumeric model valuation).mpr holds⟩
  | fof variables body =>
    intro valuation
    exact (body.holds_toNumeric model valuation).mpr (valid (fun name => valuation (variables.id name)))

theorem encode_models {named : List NamedQuantifiedEquality.Declaration} {encoded : Encoded}
    (success : encode named = .ok encoded) {D : Type} (model : Source.Interpretation D)
    (valid : NamedQuantifiedEquality.Models model named) :
    ∃ numeric : Fang.Interpretation D,
      Models (EqualityBridge.reserveInterpretation encoded.equalityId numeric) encoded.declarations := by
  obtain ⟨signature, symbols, encoding⟩ := encode_sound success
  refine ⟨model.toNumeric symbols, ?_⟩
  intro declaration member
  obtain ⟨source, sourceMember, relation⟩ := encoding.member_right member
  exact relation.valid_toNumeric model (valid source sourceMember)

theorem encode_satisfiable {named : List NamedQuantifiedEquality.Declaration} {encoded : Encoded}
    (success : encode named = .ok encoded) (sat : NamedQuantifiedEquality.Satisfiable named) :
    ReservedSatisfiable encoded.equalityId encoded.declarations := by
  obtain ⟨D, inhabited, model, valid⟩ := sat
  obtain ⟨numeric, models⟩ := encode_models success model valid
  exact ⟨D, inhabited, numeric, models⟩

theorem encode_unsat {named : List NamedQuantifiedEquality.Declaration} {encoded : Encoded}
    (success : encode named = .ok encoded)
    (refuted : ¬ ReservedSatisfiable encoded.equalityId encoded.declarations) :
    ¬ NamedQuantifiedEquality.Satisfiable named :=
  fun sat => refuted (encode_satisfiable success sat)

end Fang.QuantifiedEqualityFrontend.Encoding
