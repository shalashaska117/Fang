/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ExpandedArityTable
import Fang.SourceSemantics

namespace Fang.TptpCandidate.Arity

def termFunctions : Source.Term → List Symbol
  | .var _ => []
  | .app name arguments => (name, arguments.length) :: arguments.flatMap termFunctions

def termVariables : Source.Term → List String
  | .var name => [name]
  | .app _ arguments => arguments.flatMap termVariables

def encodeTerm (functions : Table) (variables : Source.Variables) : Source.Term → Fang.Term
  | .var name => .var (variables.id name)
  | .app name arguments => .app (id functions (name, arguments.length))
      (arguments.map (encodeTerm functions variables))

def toNumeric {D : Type} (model : Source.Interpretation D)
    (functions predicates : Table) : Fang.Interpretation D where
  function := fun index => model.function ((functions[index]?).getD ("", 0)).1
  predicate := fun index => model.predicate ((predicates[index]?).getD ("", 0)).1

def toNamed {D : Type} (model : Fang.Interpretation D)
    (functions predicates : Table) : Source.Interpretation D where
  function := fun name arguments => model.function (id functions (name, arguments.length)) arguments
  predicate := fun name arguments => model.predicate (id predicates (name, arguments.length)) arguments

def TermCovered (functions : Table) (term : Source.Term) : Prop :=
  ∀ symbol ∈ termFunctions term, symbol ∈ functions

def VariablesCovered (variables : Source.Variables) (term : Source.Term) : Prop :=
  ∀ name ∈ termVariables term, variables.name (variables.id name) = name

theorem collected_term_covered (term : Source.Term) : TermCovered (collect [] (termFunctions term)) term := by
  intro symbol member
  exact (collect_mem [] (termFunctions term) symbol).mpr (Or.inr member)

theorem term_eval_toNumeric (term : Source.Term) (functions predicates : Table)
    (variables : Source.Variables) (covered : TermCovered functions term)
    {D : Type} (model : Source.Interpretation D) (valuation : Nat → D) :
    (encodeTerm functions variables term).eval (toNumeric model functions predicates) valuation =
      term.eval model (fun name => valuation (variables.id name)) := by
  cases term with
  | var name => simp only [encodeTerm, Fang.Term.eval, Source.Term.eval]
  | app name arguments =>
    have root : (name, arguments.length) ∈ functions := covered _ (by simp [termFunctions])
    simp only [encodeTerm, Fang.Term.eval, Source.Term.eval, toNumeric, id_roundtrip root,
      Option.getD_some, List.map_map]
    apply congrArg (model.function name)
    apply List.map_congr_left
    intro child member
    apply term_eval_toNumeric child functions predicates variables
    intro symbol occurrence
    apply covered symbol
    simpa only [termFunctions] using (List.mem_cons_of_mem (name, arguments.length)
      (List.mem_flatMap.mpr ⟨child, member, occurrence⟩) :
        symbol ∈ (name, arguments.length) :: arguments.flatMap termFunctions)
termination_by sizeOf term

theorem term_eval_toNamed (term : Source.Term) (functions predicates : Table)
    (variables : Source.Variables) (covered : VariablesCovered variables term)
    {D : Type} (model : Fang.Interpretation D) (valuation : String → D) :
    term.eval (toNamed model functions predicates) valuation =
      (encodeTerm functions variables term).eval model (fun index => valuation (variables.name index)) := by
  cases term with
  | var name =>
    simp only [Source.Term.eval, encodeTerm, Fang.Term.eval, covered name (by simp [termVariables])]
  | app name arguments =>
    simp only [Source.Term.eval, encodeTerm, Fang.Term.eval, toNamed, List.length_map, List.map_map]
    apply congrArg (model.function (id functions (name, arguments.length)))
    apply List.map_congr_left
    intro child member
    apply term_eval_toNamed child functions predicates variables
    intro variableName occurrence
    apply covered variableName
    simpa only [termVariables] using (List.mem_flatMap.mpr ⟨child, member, occurrence⟩ :
      variableName ∈ arguments.flatMap termVariables)
termination_by sizeOf term

def encodeLiteral (functions predicates : Table) (variables : Source.Variables)
    (literal : Source.Literal) : Fang.Literal :=
  ⟨literal.positive, id predicates (literal.predicate, literal.arguments.length),
    literal.arguments.map (encodeTerm functions variables)⟩

def LiteralCovered (functions predicates : Table) (literal : Source.Literal) : Prop :=
  (literal.predicate, literal.arguments.length) ∈ predicates ∧
    ∀ term ∈ literal.arguments, TermCovered functions term

theorem literal_holds_toNumeric (literal : Source.Literal) (functions predicates : Table)
    (variables : Source.Variables) (covered : LiteralCovered functions predicates literal)
    {D : Type} (model : Source.Interpretation D) (valuation : Nat → D) :
    (encodeLiteral functions predicates variables literal).Holds
      (toNumeric model functions predicates) valuation ↔
      literal.Holds model (fun name => valuation (variables.id name)) := by
  have arguments : (literal.arguments.map (encodeTerm functions variables)).map
      (Fang.Term.eval (toNumeric model functions predicates) valuation) =
      literal.arguments.map (Source.Term.eval model (fun name => valuation (variables.id name))) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro term member
    exact term_eval_toNumeric term functions predicates variables (covered.2 term member) model valuation
  simp only [encodeLiteral, Fang.Literal.Holds, Fang.Atom.Holds, Source.Literal.Holds,
    toNumeric, id_roundtrip covered.1, Option.getD_some] at *
  rw [arguments]

theorem literal_holds_toNamed (literal : Source.Literal) (functions predicates : Table)
    (variables : Source.Variables)
    (covered : ∀ term ∈ literal.arguments, VariablesCovered variables term)
    {D : Type} (model : Fang.Interpretation D) (valuation : String → D) :
    literal.Holds (toNamed model functions predicates) valuation ↔
      (encodeLiteral functions predicates variables literal).Holds model
        (fun index => valuation (variables.name index)) := by
  have arguments : literal.arguments.map (Source.Term.eval (toNamed model functions predicates) valuation) =
      (literal.arguments.map (encodeTerm functions variables)).map
        (Fang.Term.eval model (fun index => valuation (variables.name index))) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro term member
    exact term_eval_toNamed term functions predicates variables (covered term member) model valuation
  simp only [Source.Literal.Holds, encodeLiteral, Fang.Literal.Holds, Fang.Atom.Holds,
    toNamed, List.length_map] at *
  rw [arguments]
  rfl

theorem signature_roundtrip {table : Table} {name : String} {arity : Nat}
    (member : (name, arity) ∈ table) :
    (table.map Prod.snd)[id table (name, arity)]? = some arity := by
  simp only [List.getElem?_map, id_roundtrip member, Option.map_some]

theorem overloaded_ids_distinct {table : Table} {name : String} {m n : Nat}
    (left : (name, m) ∈ table) (right : (name, n) ∈ table) (different : m ≠ n) :
    id table (name, m) ≠ id table (name, n) := by
  intro same
  exact different (Prod.mk.inj (id_injective left right same)).2

end Fang.TptpCandidate.Arity
