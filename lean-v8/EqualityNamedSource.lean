/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Named equality semantics and explicit name/ID transport. No byte decoder. -/
import Fang.SourceSemantics
import Trace

namespace Fang.EqualitySource

inductive Atom where
  | predicate : String → List Source.Term → Atom
  | equal : Source.Term → Source.Term → Atom

structure Literal where
  positive : Bool
  atom : Atom

structure Clause where
  name : String
  literals : List Literal

abbrev Problem := List Clause

def Atom.Holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) : Atom → Prop
  | .predicate name arguments =>
      model.predicate name (arguments.map (Source.Term.eval model valuation))
  | .equal left right => left.eval model valuation = right.eval model valuation

def Literal.Holds {D : Type} (model : Source.Interpretation D)
    (valuation : String → D) (literal : Literal) : Prop :=
  if literal.positive then literal.atom.Holds model valuation
  else ¬ literal.atom.Holds model valuation

def Clause.Valid {D : Type} (model : Source.Interpretation D) (clause : Clause) : Prop :=
  ∀ valuation, ∃ literal ∈ clause.literals, literal.Holds model valuation

def Problem.Models {D : Type} (model : Source.Interpretation D) (problem : Problem) : Prop :=
  ∀ clause ∈ problem, clause.Valid model

def Satisfiable (problem : Problem) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D), problem.Models model

/-- Predicate and function namespaces remain separate; equality has no symbol ID. -/
inductive AtomEncoding (signature : Source.Signature) (symbols : Source.Symbols)
    (variables : Source.Variables) : Atom → Equality.Atom → Prop where
  | predicate (name : String) (arguments : List Source.Term) (encoded : List Term)
      (roundtrip : symbols.predicateName (symbols.predicateId name) = name)
      (arity : signature.predicateArity name = some arguments.length)
      (children : Source.TermsEncoding signature symbols variables arguments encoded) :
      AtomEncoding signature symbols variables (.predicate name arguments)
        (.predicate ⟨symbols.predicateId name, encoded⟩)
  | equal {left right encodedLeft encodedRight}
      (leftEncoding : Source.TermEncoding signature symbols variables left encodedLeft)
      (rightEncoding : Source.TermEncoding signature symbols variables right encodedRight) :
      AtomEncoding signature symbols variables (.equal left right) (.equal encodedLeft encodedRight)

structure LiteralEncoding (signature : Source.Signature) (symbols : Source.Symbols)
    (variables : Source.Variables) (named : Literal) (encoded : Equality.Literal) : Prop where
  polarity : named.positive = encoded.positive
  atom : AtomEncoding signature symbols variables named.atom encoded.atom

abbrev ClauseEncoding (signature : Source.Signature) (symbols : Source.Symbols)
    (variables : Source.Variables) (named : Clause) (encoded : Equality.Clause) : Prop :=
  Source.RelatedLists (LiteralEncoding signature symbols variables) named.literals encoded

structure ProblemEncoding (signature : Source.Signature) (symbols : Source.Symbols)
    (named : Problem) (encoded : Equality.Problem) : Prop where
  uniqueNames : (named.map Clause.name).Nodup
  clauses : Source.RelatedLists
    (fun clause output => ∃ variables, ClauseEncoding signature symbols variables clause output)
    named encoded

theorem AtomEncoding.holds_toNumeric {signature symbols variables named encoded}
    (encoding : AtomEncoding signature symbols variables named encoded)
    {D : Type} (model : Source.Interpretation D) (valuation : Nat → D) :
    encoded.Holds (model.toNumeric symbols) valuation ↔
      named.Holds model (fun name => valuation (variables.id name)) := by
  cases encoding with
  | predicate name arguments encoded roundtrip _ children =>
    simp only [Equality.Atom.Holds, Fang.Atom.Holds, Atom.Holds]
    rw [children.eval_toNumeric model valuation]
    simp only [Source.Interpretation.toNumeric, roundtrip]
  | equal left right =>
    simp only [Equality.Atom.Holds, Atom.Holds, left.eval_toNumeric model valuation,
      right.eval_toNumeric model valuation]

theorem AtomEncoding.holds_toNamed {signature symbols variables named encoded}
    (encoding : AtomEncoding signature symbols variables named encoded)
    {D : Type} (model : Interpretation D) (valuation : String → D) :
    named.Holds (Source.numericToNamed model symbols) valuation ↔
      encoded.Holds model (fun id => valuation (variables.name id)) := by
  cases encoding with
  | predicate name arguments encoded _ _ children =>
    simp only [Equality.Atom.Holds, Fang.Atom.Holds, Atom.Holds]
    rw [children.eval_toNamed model valuation]
    rfl
  | equal left right =>
    simp only [Equality.Atom.Holds, Atom.Holds, left.eval_toNamed model valuation,
      right.eval_toNamed model valuation]

theorem LiteralEncoding.holds_toNumeric {signature symbols variables named encoded}
    (encoding : LiteralEncoding signature symbols variables named encoded)
    {D : Type} (model : Source.Interpretation D) (valuation : Nat → D) :
    encoded.Holds (model.toNumeric symbols) valuation ↔
      named.Holds model (fun name => valuation (variables.id name)) := by
  simp only [Equality.Literal.Holds, Literal.Holds, encoding.polarity,
    encoding.atom.holds_toNumeric model valuation]

theorem LiteralEncoding.holds_toNamed {signature symbols variables named encoded}
    (encoding : LiteralEncoding signature symbols variables named encoded)
    {D : Type} (model : Interpretation D) (valuation : String → D) :
    named.Holds (Source.numericToNamed model symbols) valuation ↔
      encoded.Holds model (fun id => valuation (variables.name id)) := by
  simp only [Equality.Literal.Holds, Literal.Holds, encoding.polarity,
    encoding.atom.holds_toNamed model valuation]

theorem ClauseEncoding.valid_toNumeric {signature symbols variables named encoded}
    (encoding : ClauseEncoding signature symbols variables named encoded)
    {D : Type} (model : Source.Interpretation D) (valid : named.Valid model) :
    Equality.clauseValid (model.toNumeric symbols) encoded := by
  intro valuation
  obtain ⟨literal, member, holds⟩ := valid (fun name => valuation (variables.id name))
  obtain ⟨output, outputMember, relation⟩ := encoding.member_left member
  exact ⟨output, outputMember, (relation.holds_toNumeric model valuation).mpr holds⟩

theorem ClauseEncoding.valid_toNamed {signature symbols variables named encoded}
    (encoding : ClauseEncoding signature symbols variables named encoded)
    {D : Type} (model : Interpretation D) (valid : Equality.clauseValid model encoded) :
    named.Valid (Source.numericToNamed model symbols) := by
  intro valuation
  obtain ⟨literal, member, holds⟩ := valid (fun id => valuation (variables.name id))
  obtain ⟨output, outputMember, relation⟩ := encoding.member_right member
  exact ⟨output, outputMember, (relation.holds_toNamed model valuation).mpr holds⟩

theorem ProblemEncoding.satisfiable_iff {signature symbols named encoded}
    (encoding : ProblemEncoding signature symbols named encoded) :
    Satisfiable named ↔ Equality.Satisfiable encoded := by
  constructor
  · rintro ⟨domain, inhabited, model, models⟩
    refine ⟨domain, inhabited, model.toNumeric symbols, ?_⟩
    intro clause member
    obtain ⟨source, sourceMember, variables, relation⟩ := encoding.clauses.member_right member
    exact relation.valid_toNumeric model (models source sourceMember)
  · rintro ⟨domain, inhabited, model, models⟩
    refine ⟨domain, inhabited, Source.numericToNamed model symbols, ?_⟩
    intro clause member
    obtain ⟨output, outputMember, variables, relation⟩ := encoding.clauses.member_left member
    exact relation.valid_toNamed model (models output outputMember)

/-- This needs an explicit encoding witness. No parser is assumed to supply it. -/
theorem ProblemEncoding.unsat_of_check {signature symbols named encoded}
    (encoding : ProblemEncoding signature symbols named encoded)
    (certificate : Equality.Certificate)
    (accepted : Equality.check encoded certificate = .ok ()) : ¬ Satisfiable named := by
  intro satisfiable
  exact Equality.check_refutes encoded certificate accepted (encoding.satisfiable_iff.mp satisfiable)

end Fang.EqualitySource
