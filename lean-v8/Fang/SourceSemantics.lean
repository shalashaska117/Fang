/-
Copyright (c) 2026 Pietro Pellegrino. All rights reserved.
Released under the BSD 3-Clause license; see LICENSE.

Named-source semantics and a relational contract for conversion to numeric IDs.
This module does not define a byte grammar or prove the frontend decoder correct.
-/
import Fang.Checker

namespace Fang.Source

inductive Term where
  | var : String → Term
  | app : String → List Term → Term
  deriving Repr

structure Literal where
  positive : Bool
  predicate : String
  arguments : List Term
  deriving Repr

structure Clause where
  name : String
  literals : List Literal
  deriving Repr

abbrev Problem := List Clause

structure Signature where
  functionArity : String → Option Nat
  predicateArity : String → Option Nat

structure Interpretation (D : Type) where
  function : String → List D → D
  predicate : String → List D → Prop

def Term.eval {D : Type} (model : Interpretation D) (valuation : String → D) : Term → D
  | .var name => valuation name
  | .app name arguments => model.function name (arguments.map (Term.eval model valuation))

def Literal.Holds {D : Type} (model : Interpretation D) (valuation : String → D)
    (literal : Literal) : Prop :=
  let atom := model.predicate literal.predicate
    (literal.arguments.map (Term.eval model valuation))
  if literal.positive then atom else ¬ atom

def Clause.Holds {D : Type} (model : Interpretation D) (valuation : String → D)
    (clause : Clause) : Prop :=
  ∃ literal ∈ clause.literals, literal.Holds model valuation

def Clause.Valid {D : Type} (model : Interpretation D) (clause : Clause) : Prop :=
  ∀ valuation, clause.Holds model valuation

def Problem.Models {D : Type} (model : Interpretation D) (problem : Problem) : Prop :=
  ∀ clause ∈ problem, clause.Valid model

def Satisfiable (problem : Problem) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Interpretation D), problem.Models model

/- The two symbol namespaces are independent. The relation below requires both
   directions of each assignment at every occurrence; unused entries are irrelevant. -/
structure Symbols where
  functionId : String → Nat
  functionName : Nat → String
  predicateId : String → Nat
  predicateName : Nat → String

structure Variables where
  id : String → Nat
  name : Nat → String

inductive RelatedLists (relation : α → β → Prop) : List α → List β → Prop where
  | nil : RelatedLists relation [] []
  | cons {head output tail outputs} (first : relation head output)
      (rest : RelatedLists relation tail outputs) :
      RelatedLists relation (head :: tail) (output :: outputs)

theorem RelatedLists.member_left {relation : α → β → Prop} {inputs outputs}
    (related : RelatedLists relation inputs outputs) {input : α} (member : input ∈ inputs) :
    ∃ output ∈ outputs, relation input output := by
  induction related with
  | nil => simp at member
  | @cons head output tail outputs first rest induction =>
      rcases List.mem_cons.mp member with equality | member
      · subst input; exact ⟨output, List.mem_cons_self, first⟩
      · obtain ⟨found, membership, relation⟩ := induction member
        exact ⟨found, List.mem_cons_of_mem _ membership, relation⟩

theorem RelatedLists.member_right {relation : α → β → Prop} {inputs outputs}
    (related : RelatedLists relation inputs outputs) {output : β} (member : output ∈ outputs) :
    ∃ input ∈ inputs, relation input output := by
  induction related with
  | nil => simp at member
  | @cons head output tail outputs first rest induction =>
      rcases List.mem_cons.mp member with equality | member
      · subst_vars; exact ⟨head, List.mem_cons_self, first⟩
      · obtain ⟨found, membership, relation⟩ := induction member
        exact ⟨found, List.mem_cons_of_mem _ membership, relation⟩

mutual
inductive TermEncoding (signature : Signature) (symbols : Symbols) (variables : Variables) :
    Term → Fang.Term → Prop where
  | var (name : String) (roundtrip : variables.name (variables.id name) = name) :
      TermEncoding signature symbols variables (.var name) (.var (variables.id name))
  | app (name : String) (arguments : List Term) (encoded : List Fang.Term)
      (roundtrip : symbols.functionName (symbols.functionId name) = name)
      (arity : signature.functionArity name = some arguments.length)
      (children : TermsEncoding signature symbols variables arguments encoded) :
      TermEncoding signature symbols variables (.app name arguments)
        (.app (symbols.functionId name) encoded)
inductive TermsEncoding (signature : Signature) (symbols : Symbols) (variables : Variables) :
    List Term → List Fang.Term → Prop where
  | nil : TermsEncoding signature symbols variables [] []
  | cons {term encoded terms encodedTerms}
      (head : TermEncoding signature symbols variables term encoded)
      (tail : TermsEncoding signature symbols variables terms encodedTerms) :
      TermsEncoding signature symbols variables (term :: terms) (encoded :: encodedTerms)
end

structure LiteralEncoding (signature : Signature) (symbols : Symbols) (variables : Variables)
    (literal : Literal) (encoded : Fang.Literal) : Prop where
  polarity : encoded.positive = literal.positive
  predicate : encoded.atom.pred = symbols.predicateId literal.predicate
  roundtrip : symbols.predicateName (symbols.predicateId literal.predicate) = literal.predicate
  arity : signature.predicateArity literal.predicate = some literal.arguments.length
  arguments : TermsEncoding signature symbols variables literal.arguments encoded.atom.args

abbrev ClauseEncoding (signature : Signature) (symbols : Symbols) (variables : Variables)
    (clause : Clause) (encoded : Fang.Clause) : Prop :=
  RelatedLists (LiteralEncoding signature symbols variables) clause.literals encoded

/- Each clause has its own variable assignment. Clause names identify statements;
   their uniqueness is checked separately from logical truth. -/
structure ProblemEncoding (signature : Signature) (symbols : Symbols)
    (problem : Problem) (encoded : Fang.Problem) : Prop where
  uniqueNames : (problem.map Clause.name).Nodup
  clauses : RelatedLists
    (fun clause output => ∃ variables, ClauseEncoding signature symbols variables clause output)
    problem encoded

def Interpretation.toNumeric {D : Type} (model : Interpretation D) (symbols : Symbols) :
    Fang.Interpretation D :=
  ⟨fun id => model.function (symbols.functionName id),
   fun id => model.predicate (symbols.predicateName id)⟩

def numericToNamed {D : Type} (model : Fang.Interpretation D) (symbols : Symbols) :
    Interpretation D :=
  ⟨fun name => model.function (symbols.functionId name),
   fun name => model.predicate (symbols.predicateId name)⟩

mutual
theorem TermEncoding.eval_toNumeric {signature symbols variables named encoded}
    (encoding : TermEncoding signature symbols variables named encoded)
    {D : Type} (model : Interpretation D) (valuation : Nat → D) :
    encoded.eval (model.toNumeric symbols) valuation =
      named.eval model (fun name => valuation (variables.id name)) := by
  cases encoding with
  | var name _ => simp only [Fang.Term.eval, Term.eval]
  | app name arguments encoded roundtrip _ children =>
      simp only [Fang.Term.eval, Term.eval, Interpretation.toNumeric, roundtrip]
      exact congrArg (model.function name) (children.eval_toNumeric model valuation)
theorem TermsEncoding.eval_toNumeric {signature symbols variables named encoded}
    (encoding : TermsEncoding signature symbols variables named encoded)
    {D : Type} (model : Interpretation D) (valuation : Nat → D) :
    encoded.map (Fang.Term.eval (model.toNumeric symbols) valuation) =
      named.map (Term.eval model (fun name => valuation (variables.id name))) := by
  cases encoding with
  | nil => rfl
  | cons head tail =>
      simp only [List.map_cons, head.eval_toNumeric model valuation,
        tail.eval_toNumeric model valuation]
end

mutual
theorem TermEncoding.eval_toNamed {signature symbols variables named encoded}
    (encoding : TermEncoding signature symbols variables named encoded)
    {D : Type} (model : Fang.Interpretation D) (valuation : String → D) :
    named.eval (numericToNamed model symbols) valuation =
      encoded.eval model (fun id => valuation (variables.name id)) := by
  cases encoding with
  | var name roundtrip => simp only [Term.eval, Fang.Term.eval, roundtrip]
  | app name arguments encoded _ _ children =>
      simp only [Term.eval, Fang.Term.eval, numericToNamed]
      exact congrArg (model.function (symbols.functionId name))
        (children.eval_toNamed model valuation)
theorem TermsEncoding.eval_toNamed {signature symbols variables named encoded}
    (encoding : TermsEncoding signature symbols variables named encoded)
    {D : Type} (model : Fang.Interpretation D) (valuation : String → D) :
    named.map (Term.eval (numericToNamed model symbols) valuation) =
      encoded.map (Fang.Term.eval model (fun id => valuation (variables.name id))) := by
  cases encoding with
  | nil => rfl
  | cons head tail =>
      simp only [List.map_cons, head.eval_toNamed model valuation,
        tail.eval_toNamed model valuation]
end

theorem LiteralEncoding.holds_toNumeric {signature symbols variables named encoded}
    (encoding : LiteralEncoding signature symbols variables named encoded)
    {D : Type} (model : Interpretation D) (valuation : Nat → D) :
    encoded.Holds (model.toNumeric symbols) valuation ↔
      named.Holds model (fun name => valuation (variables.id name)) := by
  simp only [Fang.Literal.Holds, Fang.Atom.Holds, Literal.Holds]
  rw [encoding.arguments.eval_toNumeric model valuation]
  simp only [encoding.polarity, encoding.predicate, Interpretation.toNumeric, encoding.roundtrip]

theorem LiteralEncoding.holds_toNamed {signature symbols variables named encoded}
    (encoding : LiteralEncoding signature symbols variables named encoded)
    {D : Type} (model : Fang.Interpretation D) (valuation : String → D) :
    named.Holds (numericToNamed model symbols) valuation ↔
      encoded.Holds model (fun id => valuation (variables.name id)) := by
  simp only [Fang.Literal.Holds, Fang.Atom.Holds, Literal.Holds]
  rw [encoding.arguments.eval_toNamed model valuation]
  simp only [encoding.polarity, encoding.predicate, numericToNamed]

theorem ClauseEncoding.valid_toNumeric {signature symbols variables named encoded}
    (encoding : ClauseEncoding signature symbols variables named encoded)
    {D : Type} (model : Interpretation D) (valid : named.Valid model) :
    encoded.Valid (model.toNumeric symbols) := by
  intro valuation
  obtain ⟨literal, member, holds⟩ := valid (fun name => valuation (variables.id name))
  obtain ⟨output, outputMember, relation⟩ := encoding.member_left member
  exact ⟨output, outputMember, (relation.holds_toNumeric model valuation).mpr holds⟩

theorem ClauseEncoding.valid_toNamed {signature symbols variables named encoded}
    (encoding : ClauseEncoding signature symbols variables named encoded)
    {D : Type} (model : Fang.Interpretation D) (valid : encoded.Valid model) :
    named.Valid (numericToNamed model symbols) := by
  intro valuation
  obtain ⟨literal, member, holds⟩ := valid (fun id => valuation (variables.name id))
  obtain ⟨output, outputMember, relation⟩ := encoding.member_right member
  exact ⟨output, outputMember, (relation.holds_toNamed model valuation).mpr holds⟩

theorem ProblemEncoding.satisfiable_iff {signature symbols named encoded}
    (encoding : ProblemEncoding signature symbols named encoded) :
    Satisfiable named ↔ Fang.Satisfiable encoded := by
  constructor
  · rintro ⟨domain, inhabited, model, models⟩
    refine ⟨domain, inhabited, model.toNumeric symbols, ?_⟩
    intro clause member
    obtain ⟨source, sourceMember, variables, relation⟩ :=
      encoding.clauses.member_right member
    exact relation.valid_toNumeric model (models source sourceMember)
  · rintro ⟨domain, inhabited, model, models⟩
    refine ⟨domain, inhabited, numericToNamed model symbols, ?_⟩
    intro clause member
    obtain ⟨output, outputMember, variables, relation⟩ :=
      encoding.clauses.member_left member
    exact relation.valid_toNamed model (models output outputMember)

theorem ProblemEncoding.unsat_of_check {signature symbols named encoded}
    (encoding : ProblemEncoding signature symbols named encoded)
    (certificate : Fang.Certificate)
    (accepted : Fang.check (Fang.preprocess encoded) certificate = true) :
    ¬ Satisfiable named := by
  intro satisfiable
  exact Fang.check_preprocessed_sound encoded certificate accepted
    (encoding.satisfiable_iff.mp satisfiable)

#print axioms ProblemEncoding.satisfiable_iff
#print axioms ProblemEncoding.unsat_of_check

end Fang.Source
