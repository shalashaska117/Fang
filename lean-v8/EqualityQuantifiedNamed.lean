/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent named equality semantics and reserved-head encoding specification.
   No executable parser or Rust lowering refinement is asserted here. -/
import QuantifiedEncoding
import SemanticModel

namespace Fang.NamedQuantifiedEquality

inductive Atom where
  | predicate : String → List Source.Term → Atom
  | equal : Source.Term → Source.Term → Atom

inductive Formula where
  | atom : Atom → Formula
  | truth | falsity
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  | all : String → Formula → Formula
  | ex : String → Formula → Formula

def Atom.Holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) : Atom → Prop
  | .predicate name arguments => model.predicate name (arguments.map (Source.Term.eval model valuation))
  | .equal left right => left.eval model valuation = right.eval model valuation

def Formula.Holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) : Formula → Prop
  | .atom value => value.Holds model valuation
  | .truth => True
  | .falsity => False
  | .neg body => ¬ body.Holds model valuation
  | .conj left right => left.Holds model valuation ∧ right.Holds model valuation
  | .disj left right => left.Holds model valuation ∨ right.Holds model valuation
  | .implies left right => left.Holds model valuation → right.Holds model valuation
  | .all binder body => ∀ value, body.Holds model (NamedQuantified.update valuation binder value)
  | .ex binder body => ∃ value, body.Holds model (NamedQuantified.update valuation binder value)

def Atom.Within (bound : List String) : Atom → Prop
  | .predicate _ arguments => ∀ term ∈ arguments, NamedQuantified.TermWithin bound term
  | .equal left right => NamedQuantified.TermWithin bound left ∧ NamedQuantified.TermWithin bound right

def Formula.Within (bound : List String) : Formula → Prop
  | .atom value => value.Within bound
  | .truth | .falsity => True
  | .neg body => body.Within bound
  | .conj left right | .disj left right | .implies left right => left.Within bound ∧ right.Within bound
  | .all name body | .ex name body => body.Within (name :: bound)

/-- The ordinary-head bound prevents a source predicate from denoting equality.
    Both equality operands are terms; the reserved head has exactly two arguments. -/
inductive AtomEncoding (reserved : Nat) (signature : Source.Signature) (symbols : Source.Symbols)
    (variables : Source.Variables) : Atom → Fang.Atom → Prop where
  | predicate (name : String) (arguments : List Source.Term) (encoded : List Fang.Term)
      (roundtrip : symbols.predicateName (symbols.predicateId name) = name)
      (arity : signature.predicateArity name = some arguments.length)
      (ordinary : symbols.predicateId name < reserved)
      (terms : Source.TermsEncoding signature symbols variables arguments encoded) :
      AtomEncoding reserved signature symbols variables (.predicate name arguments)
        ⟨symbols.predicateId name, encoded⟩
  | equal {left right encodedLeft encodedRight}
      (first : Source.TermEncoding signature symbols variables left encodedLeft)
      (second : Source.TermEncoding signature symbols variables right encodedRight) :
      AtomEncoding reserved signature symbols variables (.equal left right) ⟨reserved, [encodedLeft, encodedRight]⟩

inductive Encoding (reserved : Nat) (signature : Source.Signature) (symbols : Source.Symbols)
    (variables : Source.Variables) : Formula → QuantifiedFOF.Formula → Prop where
  | atom {source target} (encoded : AtomEncoding reserved signature symbols variables source target) :
      Encoding reserved signature symbols variables (.atom source) (.atom target)
  | truth : Encoding reserved signature symbols variables .truth .truth
  | falsity : Encoding reserved signature symbols variables .falsity .falsity
  | neg {source target} (child : Encoding reserved signature symbols variables source target) :
      Encoding reserved signature symbols variables (.neg source) (.neg target)
  | conj {left right l r} (first : Encoding reserved signature symbols variables left l)
      (second : Encoding reserved signature symbols variables right r) :
      Encoding reserved signature symbols variables (.conj left right) (.conj l r)
  | disj {left right l r} (first : Encoding reserved signature symbols variables left l)
      (second : Encoding reserved signature symbols variables right r) :
      Encoding reserved signature symbols variables (.disj left right) (.disj l r)
  | implies {left right l r} (first : Encoding reserved signature symbols variables left l)
      (second : Encoding reserved signature symbols variables right r) :
      Encoding reserved signature symbols variables (.implies left right) (.implies l r)
  | all (name : String) {source target} (roundtrip : variables.name (variables.id name) = name)
      (child : Encoding reserved signature symbols variables source target) :
      Encoding reserved signature symbols variables (.all name source) (.all (variables.id name) target)
  | ex (name : String) {source target} (roundtrip : variables.name (variables.id name) = name)
      (child : Encoding reserved signature symbols variables source target) :
      Encoding reserved signature symbols variables (.ex name source) (.ex (variables.id name) target)

theorem AtomEncoding.holds {reserved signature symbols variables source target}
    (encoding : AtomEncoding reserved signature symbols variables source target)
    {D : Type} {named : Source.Interpretation D} {numeric : Fang.Interpretation D}
    (models : NamedQuantified.InterpretationsAgree symbols named numeric)
    {namedValuation : String → D} {numericValuation : Nat → D}
    (values : NamedQuantified.ValuationsAgree variables namedValuation numericValuation) :
    target.Holds (EqualityBridge.reserveInterpretation reserved numeric) numericValuation ↔
      source.Holds named namedValuation := by
  have terms : Fang.Term.eval (EqualityBridge.reserveInterpretation reserved numeric) numericValuation =
      Fang.Term.eval numeric numericValuation :=
    funext (EqualityBridge.term_eval_reserved reserved numeric numericValuation)
  cases encoding with
  | predicate name arguments encoded roundtrip _ ordinary children =>
    have different : symbols.predicateId name ≠ reserved := Nat.ne_of_lt ordinary
    simp only [Fang.Atom.Holds, Atom.Holds, terms]
    rw [NamedQuantified.terms_encoding_eval children models values]
    simp only [EqualityBridge.reserveInterpretation, different, ↓reduceIte]
    exact models.predicate name roundtrip _
  | @equal left right encodedLeft encodedRight first second =>
    calc
      _ ↔ encodedLeft.eval numeric numericValuation = encodedRight.eval numeric numericValuation :=
        EqualityBridge.atom_encoding_holds reserved numeric numericValuation
          (.equal encodedLeft encodedRight) trivial
      _ ↔ left.eval named namedValuation = right.eval named namedValuation := by
        rw [NamedQuantified.term_encoding_eval first models values,
          NamedQuantified.term_encoding_eval second models values]

theorem Encoding.holds {reserved signature symbols variables source target}
    (encoding : Encoding reserved signature symbols variables source target)
    {D : Type} {named : Source.Interpretation D} {numeric : Fang.Interpretation D}
    (models : NamedQuantified.InterpretationsAgree symbols named numeric)
    (namedValuation : String → D) (numericValuation : Nat → D)
    (values : NamedQuantified.ValuationsAgree variables namedValuation numericValuation) :
    target.Holds (EqualityBridge.reserveInterpretation reserved numeric) numericValuation ↔
      source.Holds named namedValuation := by
  induction encoding generalizing namedValuation numericValuation with
  | atom encoded => exact encoded.holds models values
  | truth | falsity => rfl
  | neg _ ih => exact not_congr (ih _ _ values)
  | conj _ _ il ir => exact and_congr (il _ _ values) (ir _ _ values)
  | disj _ _ il ir => exact or_congr (il _ _ values) (ir _ _ values)
  | implies _ _ il ir => exact imp_congr (il _ _ values) (ir _ _ values)
  | all name roundtrip _ ih => exact forall_congr' (fun value => ih _ _ (values.update name roundtrip value))
  | ex name roundtrip _ ih => exact exists_congr (fun value => ih _ _ (values.update name roundtrip value))

theorem Encoding.holds_toNumeric {reserved signature symbols variables source target}
    (encoding : Encoding reserved signature symbols variables source target)
    {D : Type} (model : Source.Interpretation D) (valuation : Nat → D) :
    target.Holds (EqualityBridge.reserveInterpretation reserved (model.toNumeric symbols)) valuation ↔
      source.Holds model (fun name => valuation (variables.id name)) :=
  encoding.holds (NamedQuantified.InterpretationsAgree.toNumeric symbols model) _ _ (fun _ _ => rfl)

theorem AtomEncoding.within {reserved signature symbols variables source target}
    (encoding : AtomEncoding reserved signature symbols variables source target)
    (bound : List String) (scope : source.Within bound) :
    ∀ term ∈ target.args, QuantifiedFOF.TermWithin (bound.map variables.id) term := by
  cases encoding with
  | predicate _ _ _ _ _ _ children => exact NamedQuantified.terms_encoding_within children bound scope
  | equal first second =>
    intro term member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact NamedQuantified.term_encoding_within first bound scope.1
    · exact NamedQuantified.term_encoding_within second bound scope.2

theorem Encoding.within {reserved signature symbols variables source target}
    (encoding : Encoding reserved signature symbols variables source target)
    (bound : List String) (scope : source.Within bound) : target.Within (bound.map variables.id) := by
  induction encoding generalizing bound with
  | atom encoded => exact encoded.within bound scope
  | truth | falsity => trivial
  | neg _ ih => exact ih bound scope
  | conj _ _ il ir | disj _ _ il ir | implies _ _ il ir => exact ⟨il bound scope.1, ir bound scope.2⟩
  | all name _ _ ih | ex name _ _ ih => exact ih (name :: bound) scope

end Fang.NamedQuantifiedEquality
