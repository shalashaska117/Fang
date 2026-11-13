/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent named-input semantics. This is not a Rust parser proof. -/
import Fang.SourceSemantics
import QuantifiedFormula

namespace Fang.NamedQuantified

inductive Formula where
  | atom : String → List Source.Term → Formula
  | truth | falsity
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | implies : Formula → Formula → Formula
  | all : String → Formula → Formula
  | ex : String → Formula → Formula
  deriving Repr

def update {D : Type} (valuation : String → D) (binder : String) (value : D) : String → D :=
  fun other => if other = binder then value else valuation other

def Formula.Holds {D : Type} (M : Source.Interpretation D) (valuation : String → D) : Formula → Prop
  | .atom name args => M.predicate name (args.map (Source.Term.eval M valuation))
  | .truth => True
  | .falsity => False
  | .neg body => ¬ body.Holds M valuation
  | .conj left right => left.Holds M valuation ∧ right.Holds M valuation
  | .disj left right => left.Holds M valuation ∨ right.Holds M valuation
  | .implies left right => left.Holds M valuation → right.Holds M valuation
  | .all binder body => ∀ value : D, body.Holds M (update valuation binder value)
  | .ex binder body => ∃ value : D, body.Holds M (update valuation binder value)

def TermWithin (bound : List String) : Source.Term → Prop
  | .var name => name ∈ bound
  | .app _ args => ∀ term ∈ args, TermWithin bound term

def Formula.Within (bound : List String) : Formula → Prop
  | .atom _ args => ∀ term ∈ args, TermWithin bound term
  | .truth | .falsity => True
  | .neg body => body.Within bound
  | .conj left right | .disj left right | .implies left right =>
      left.Within bound ∧ right.Within bound
  | .all name body | .ex name body => body.Within (name :: bound)

/-- Each binder occurrence remains, including unused and shadowed occurrences.
    The numeric ID still identifies a source spelling, before rectification. -/
inductive Encoding (signature : Source.Signature) (symbols : Source.Symbols)
    (variables : Source.Variables) : Formula → QuantifiedFOF.Formula → Prop where
  | atom (name : String) (args : List Source.Term) (encoded : List Fang.Term)
      (roundtrip : symbols.predicateName (symbols.predicateId name) = name)
      (arity : signature.predicateArity name = some args.length)
      (terms : Source.TermsEncoding signature symbols variables args encoded) :
      Encoding signature symbols variables (.atom name args) (.atom ⟨symbols.predicateId name, encoded⟩)
  | truth : Encoding signature symbols variables .truth .truth
  | falsity : Encoding signature symbols variables .falsity .falsity
  | neg {body output} (child : Encoding signature symbols variables body output) :
      Encoding signature symbols variables (.neg body) (.neg output)
  | conj {left right l r} (first : Encoding signature symbols variables left l)
      (second : Encoding signature symbols variables right r) :
      Encoding signature symbols variables (.conj left right) (.conj l r)
  | disj {left right l r} (first : Encoding signature symbols variables left l)
      (second : Encoding signature symbols variables right r) :
      Encoding signature symbols variables (.disj left right) (.disj l r)
  | implies {left right l r} (first : Encoding signature symbols variables left l)
      (second : Encoding signature symbols variables right r) :
      Encoding signature symbols variables (.implies left right) (.implies l r)
  | all (name : String) {body output}
      (roundtrip : variables.name (variables.id name) = name)
      (child : Encoding signature symbols variables body output) :
      Encoding signature symbols variables (.all name body) (.all (variables.id name) output)
  | ex (name : String) {body output}
      (roundtrip : variables.name (variables.id name) = name)
      (child : Encoding signature symbols variables body output) :
      Encoding signature symbols variables (.ex name body) (.ex (variables.id name) output)

/-- Only represented names require agreement. No global bijection is assumed
    for fallback entries outside the finite source variable table. -/
def ValuationsAgree {D : Type} (variables : Source.Variables)
    (named : String → D) (numeric : Nat → D) : Prop :=
  ∀ name, variables.name (variables.id name) = name → named name = numeric (variables.id name)

structure InterpretationsAgree {D : Type} (symbols : Source.Symbols)
    (named : Source.Interpretation D) (numeric : Fang.Interpretation D) : Prop where
  function : ∀ name, symbols.functionName (symbols.functionId name) = name →
    ∀ args, numeric.function (symbols.functionId name) args = named.function name args
  predicate : ∀ name, symbols.predicateName (symbols.predicateId name) = name →
    ∀ args, numeric.predicate (symbols.predicateId name) args ↔ named.predicate name args

theorem roundtrip_ids_distinct (variables : Source.Variables) {left right : String}
    (l : variables.name (variables.id left) = left)
    (r : variables.name (variables.id right) = right) (different : left ≠ right) :
    variables.id left ≠ variables.id right := by
  intro same
  exact different (l.symm.trans ((congrArg variables.name same).trans r))

theorem ValuationsAgree.update {D : Type} {variables : Source.Variables}
    {named : String → D} {numeric : Nat → D} (agree : ValuationsAgree variables named numeric)
    (binder : String) (roundtrip : variables.name (variables.id binder) = binder) (value : D) :
    ValuationsAgree variables (update named binder value)
      (QuantifiedFOF.update numeric (variables.id binder) value) := by
  intro name represented
  by_cases same : name = binder
  · subst name
    simp [Fang.NamedQuantified.update, QuantifiedFOF.update]
  · have distinct := roundtrip_ids_distinct variables represented roundtrip same
    simpa [Fang.NamedQuantified.update, QuantifiedFOF.update, same, distinct] using agree name represented

theorem InterpretationsAgree.toNumeric {D : Type} (symbols : Source.Symbols)
    (named : Source.Interpretation D) : InterpretationsAgree symbols named (named.toNumeric symbols) := by
  constructor
  · intro name roundtrip args
    simp only [Source.Interpretation.toNumeric, roundtrip]
  · intro name roundtrip args
    simp only [Source.Interpretation.toNumeric, roundtrip]

theorem InterpretationsAgree.toNamed {D : Type} (symbols : Source.Symbols)
    (numeric : Fang.Interpretation D) : InterpretationsAgree symbols (Source.numericToNamed numeric symbols) numeric := by
  constructor
  · intro name _ args; rfl
  · intro name _ args; rfl

end Fang.NamedQuantified
