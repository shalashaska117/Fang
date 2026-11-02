/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import QuantifiedNamed

namespace Fang.NamedQuantified

mutual
theorem term_encoding_eval {signature symbols variables source target}
    (encoding : Source.TermEncoding signature symbols variables source target)
    {D : Type} {named : Source.Interpretation D} {numeric : Fang.Interpretation D}
    (models : InterpretationsAgree symbols named numeric)
    {namedValuation : String → D} {numericValuation : Nat → D}
    (values : ValuationsAgree variables namedValuation numericValuation) :
    target.eval numeric numericValuation = source.eval named namedValuation := by
  cases encoding with
  | var name roundtrip =>
    simpa only [Fang.Term.eval, Source.Term.eval] using (values name roundtrip).symm
  | app name args encoded roundtrip _ children =>
    simp only [Fang.Term.eval, Source.Term.eval]
    rw [terms_encoding_eval children models values]
    exact models.function name roundtrip _

theorem terms_encoding_eval {signature symbols variables source target}
    (encoding : Source.TermsEncoding signature symbols variables source target)
    {D : Type} {named : Source.Interpretation D} {numeric : Fang.Interpretation D}
    (models : InterpretationsAgree symbols named numeric)
    {namedValuation : String → D} {numericValuation : Nat → D}
    (values : ValuationsAgree variables namedValuation numericValuation) :
    target.map (Fang.Term.eval numeric numericValuation) =
      source.map (Source.Term.eval named namedValuation) := by
  cases encoding with
  | nil => rfl
  | cons head tail =>
    simp only [List.map_cons, term_encoding_eval head models values,
      terms_encoding_eval tail models values]
end

theorem Encoding.holds {signature symbols variables source target}
    (encoding : Encoding signature symbols variables source target)
    {D : Type} {named : Source.Interpretation D} {numeric : Fang.Interpretation D}
    (models : InterpretationsAgree symbols named numeric)
    (namedValuation : String → D) (numericValuation : Nat → D)
    (values : ValuationsAgree variables namedValuation numericValuation) :
    target.Holds numeric numericValuation ↔ source.Holds named namedValuation := by
  induction encoding generalizing namedValuation numericValuation with
  | atom name args encoded roundtrip _ terms =>
    simp only [QuantifiedFOF.Formula.Holds, Fang.Atom.Holds, Formula.Holds]
    rw [terms_encoding_eval terms models values]
    exact models.predicate name roundtrip _
  | truth => rfl
  | falsity => rfl
  | neg _ ih => exact not_congr (ih _ _ values)
  | conj _ _ il ir => exact and_congr (il _ _ values) (ir _ _ values)
  | disj _ _ il ir => exact or_congr (il _ _ values) (ir _ _ values)
  | implies _ _ il ir => exact imp_congr (il _ _ values) (ir _ _ values)
  | all name roundtrip _ ih =>
    exact forall_congr' (fun value => ih _ _ (values.update name roundtrip value))
  | ex name roundtrip _ ih =>
    exact exists_congr (fun value => ih _ _ (values.update name roundtrip value))

theorem Encoding.holds_toNumeric {signature symbols variables source target}
    (encoding : Encoding signature symbols variables source target)
    {D : Type} (model : Source.Interpretation D) (valuation : Nat → D) :
    target.Holds (model.toNumeric symbols) valuation ↔
      source.Holds model (fun name => valuation (variables.id name)) :=
  encoding.holds (InterpretationsAgree.toNumeric symbols model) _ _ (fun _ _ => rfl)

theorem Encoding.holds_toNamed {signature symbols variables source target}
    (encoding : Encoding signature symbols variables source target)
    {D : Type} (model : Fang.Interpretation D) (valuation : String → D) :
    source.Holds (Source.numericToNamed model symbols) valuation ↔
      target.Holds model (fun id => valuation (variables.name id)) := by
  symm
  apply encoding.holds (InterpretationsAgree.toNamed symbols model)
  intro name roundtrip
  simp only [roundtrip]

mutual
theorem term_encoding_within {signature symbols variables source target}
    (encoding : Source.TermEncoding signature symbols variables source target)
    (bound : List String) (scope : TermWithin bound source) :
    QuantifiedFOF.TermWithin (bound.map variables.id) target := by
  cases encoding with
  | var name _ =>
    simp only [TermWithin] at scope
    simp only [QuantifiedFOF.TermWithin]
    exact List.mem_map.mpr ⟨name, scope, rfl⟩
  | app name args encoded _ _ children =>
    simp only [TermWithin] at scope
    simp only [QuantifiedFOF.TermWithin]
    exact terms_encoding_within children bound scope

theorem terms_encoding_within {signature symbols variables source target}
    (encoding : Source.TermsEncoding signature symbols variables source target)
    (bound : List String) (scope : ∀ term ∈ source, TermWithin bound term) :
    ∀ term ∈ target, QuantifiedFOF.TermWithin (bound.map variables.id) term := by
  cases encoding with
  | nil => simp
  | cons head tail =>
    intro term member
    rcases List.mem_cons.mp member with same | member
    · subst term
      exact term_encoding_within head bound (scope _ List.mem_cons_self)
    · exact terms_encoding_within tail bound
        (fun t ht => scope t (List.mem_cons_of_mem _ ht)) term member
end

theorem Encoding.within {signature symbols variables source target}
    (encoding : Encoding signature symbols variables source target)
    (bound : List String) (scope : source.Within bound) :
    target.Within (bound.map variables.id) := by
  induction encoding generalizing bound with
  | atom _ _ _ _ _ terms => exact terms_encoding_within terms bound scope
  | truth => trivial
  | falsity => trivial
  | neg _ ih => exact ih bound scope
  | conj _ _ il ir => exact ⟨il bound scope.1, ir bound scope.2⟩
  | disj _ _ il ir => exact ⟨il bound scope.1, ir bound scope.2⟩
  | implies _ _ il ir => exact ⟨il bound scope.1, ir bound scope.2⟩
  | all name _ _ ih => exact ih (name :: bound) scope
  | ex name _ _ ih => exact ih (name :: bound) scope

end Fang.NamedQuantified
