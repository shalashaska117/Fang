/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import RoleUnique

namespace Fang.TptpCandidate.Roles.Bytes
open FullFof

/-- Semantic records retain the original label, role and unnegated formula.
    The actual Entry separately retains the complete original byte metadata. -/
def source (values : List Entry) : List (Roles.Declaration Name FullFof.Formula) :=
  values.map (fun value => ⟨value.original.name, value.role, value.original.body.formula⟩)

theorem byteParsed_source_unique {input maximum left right}
    (first : ByteParsed input maximum left) (second : ByteParsed input maximum right) :
    source left = source right := by
  have same := congrArg (List.map (fun value : Name × Role × FullFof.Body =>
      (⟨value.1, value.2.1, value.2.2.formula⟩ : Roles.Declaration Name FullFof.Formula)))
    (byteParsed_content_unique first second)
  simpa only [contents, source, List.map_map, Function.comp_def] using same

/-- Source CNF has universal closure. Accepted FOF goals are already closed. -/
def sentence {D : Type} (model : Source.Interpretation D) (formula : FullFof.Formula) : Prop :=
  ∀ valuation, formula.Holds model valuation

def BytesEntailsIn (input : List UInt8) (maximum : Nat) (D : Type) : Prop :=
  ∃ values, ByteParsed input maximum values ∧ Closed values ∧
    Roles.EntailsAll (sentence (D := D)) (source values)

/-- Original-byte entailment of every original conjecture. This is a semantic
    proposition, not an executable SZS result or a checker acceptance claim. -/
def BytesEntailsAll (input : List UInt8) (maximum : Nat := 1048576) : Prop :=
  ∀ (D : Type) (_ : Nonempty D), BytesEntailsIn input maximum D

theorem decode_entails_in {input maximum values}
    (success : decodeBytes input maximum = .ok values) (D : Type) :
    BytesEntailsIn input maximum D ↔ Roles.EntailsAll (sentence (D := D)) (source values) := by
  constructor
  · rintro ⟨other, parsed, _, entails⟩
    have same := byteParsed_source_unique parsed (decode_grammar success)
    simpa only [same] using entails
  · intro entails
    exact ⟨values, decode_grammar success, decode_closed success, entails⟩

theorem decode_entails_all {input maximum values}
    (success : decodeBytes input maximum = .ok values) :
    BytesEntailsAll input maximum ↔
      ∀ (D : Type) (_ : Nonempty D), Roles.EntailsAll (sentence (D := D)) (source values) := by
  constructor
  · intro entails D inhabited
    exact (decode_entails_in success D).mp (entails D inhabited)
  · intro entails D inhabited
    exact (decode_entails_in success D).mpr (entails D inhabited)

/-- Each original conjecture needs its own refutation. The refutation premise
    here is semantic; an actual signed preprocessing/checker connection remains
    a separate obligation. No other conjecture is used as a premise. -/
theorem decode_all_refuted_iff {input maximum values}
    (success : decodeBytes input maximum = .ok values) :
    (∀ (D : Type) (_ : Nonempty D), ∀ goal ∈ goals (source values),
      ¬ ∃ model : Source.Interpretation D, Countermodel sentence (source values) goal model) ↔
      BytesEntailsAll input maximum := by
  rw [decode_entails_all success]
  constructor
  · intro refuted D inhabited
    exact (all_refuted_iff_entails_all sentence (source values)).mp (refuted D inhabited)
  · intro entails D inhabited
    exact (all_refuted_iff_entails_all sentence (source values)).mpr (entails D inhabited)

/-- The satisfiability mode has no original conjecture. Already-negated inputs
    remain positive constraints and do not identify an original goal. -/
def BytesInputsSatisfiable (input : List UInt8) (maximum : Nat := 1048576) : Prop :=
  ∃ values, ByteParsed input maximum values ∧ Closed values ∧ goals (source values) = [] ∧
    ∃ (D : Type) (_ : Nonempty D), SatisfiableInputs (sentence (D := D)) (source values)

theorem decode_inputs_satisfiable {input maximum values}
    (success : decodeBytes input maximum = .ok values) (noGoals : goals (source values) = []) :
    BytesInputsSatisfiable input maximum ↔
      ∃ (D : Type) (_ : Nonempty D), SatisfiableInputs (sentence (D := D)) (source values) := by
  constructor
  · rintro ⟨other, parsed, _, _, models⟩
    have same := byteParsed_source_unique parsed (decode_grammar success)
    simpa only [same] using models
  · intro models
    exact ⟨values, decode_grammar success, decode_closed success, noGoals, models⟩

end Fang.TptpCandidate.Roles.Bytes
