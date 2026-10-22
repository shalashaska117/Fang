/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
Independent fixed-signature source validity. Grammar recognition alone does not
establish consistent arities or unique clause names.
-/
import Fang.SourceLexing

namespace Fang.Source

mutual
def Term.WellFormed (signature : Signature) : Term → Prop
  | .var _ => True
  | .app name arguments => signature.functionArity name = some arguments.length ∧
      TermsWellFormed signature arguments

def TermsWellFormed (signature : Signature) : List Term → Prop
  | [] => True
  | head :: tail => head.WellFormed signature ∧ TermsWellFormed signature tail
end

def Literal.WellFormed (signature : Signature) (literal : Literal) : Prop :=
  signature.predicateArity literal.predicate = some literal.arguments.length ∧
    TermsWellFormed signature literal.arguments

def Clause.WellFormed (signature : Signature) (clause : Clause) : Prop :=
  ∀ literal ∈ clause.literals, literal.WellFormed signature

def Problem.WellFormed (signature : Signature) (problem : Problem) : Prop :=
  (problem.map Clause.name).Nodup ∧ ∀ clause ∈ problem, clause.WellFormed signature

mutual
theorem TermEncoding.wellFormed {signature symbols variables term encoded}
    (encoding : TermEncoding signature symbols variables term encoded) :
    term.WellFormed signature := by
  cases encoding with
  | var => trivial
  | app name arguments encoded roundtrip arity children =>
      exact ⟨arity, children.wellFormed⟩

theorem TermsEncoding.wellFormed {signature symbols variables terms encoded}
    (encoding : TermsEncoding signature symbols variables terms encoded) :
    TermsWellFormed signature terms := by
  cases encoding with
  | nil => trivial
  | cons head tail => exact ⟨head.wellFormed, tail.wellFormed⟩
end

theorem LiteralEncoding.wellFormed {signature symbols variables literal encoded}
    (encoding : LiteralEncoding signature symbols variables literal encoded) :
    literal.WellFormed signature :=
  ⟨encoding.arity, encoding.arguments.wellFormed⟩

theorem ClauseEncoding.wellFormed {signature symbols variables clause encoded}
    (encoding : ClauseEncoding signature symbols variables clause encoded) :
    clause.WellFormed signature := by
  intro literal member
  obtain ⟨output, _, related⟩ := encoding.member_left member
  exact related.wellFormed

theorem ProblemEncoding.wellFormed {signature symbols problem encoded}
    (encoding : ProblemEncoding signature symbols problem encoded) :
    problem.WellFormed signature := by
  refine ⟨encoding.uniqueNames, ?_⟩
  intro clause member
  obtain ⟨output, _, variables, related⟩ := encoding.clauses.member_left member
  exact related.wellFormed

theorem Term.WellFormed.same_arity {signature name left right}
    (first : (Term.app name left).WellFormed signature)
    (second : (Term.app name right).WellFormed signature) : left.length = right.length := by
  exact Option.some.inj (first.1.symm.trans second.1)

theorem Literal.WellFormed.same_arity {signature : Signature} {first second : Literal}
    (left : first.WellFormed signature) (right : second.WellFormed signature)
    (same : first.predicate = second.predicate) :
    first.arguments.length = second.arguments.length := by
  have arity := left.1
  rw [same] at arity
  exact Option.some.inj (arity.symm.trans right.1)

theorem Problem.WellFormed.unique_names {signature : Signature} {problem : Problem}
    (valid : problem.WellFormed signature) : (problem.map Clause.name).Nodup :=
  valid.1

namespace Grammar

/-- The declared source language includes semantic formation conditions.
    This predicate depends on the independent grammar, not an executable decoder. -/
def ValidInput (bytes : Bytes) : Prop :=
  ∃ problem signature, Parses bytes problem ∧ problem.WellFormed signature

theorem validInput_of_encoding {bytes problem signature symbols encoded}
    (parsed : Parses bytes problem)
    (encoding : ProblemEncoding signature symbols problem encoded) :
    ValidInput bytes :=
  ⟨problem, signature, parsed, encoding.wellFormed⟩

end Grammar

#print axioms TermEncoding.wellFormed
#print axioms ProblemEncoding.wellFormed
#print axioms Term.WellFormed.same_arity
#print axioms Literal.WellFormed.same_arity
#print axioms Grammar.validInput_of_encoding

end Fang.Source
