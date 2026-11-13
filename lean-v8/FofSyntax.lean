/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Independent surface syntax preserves source order before connective lowering. -/
import ArityProblem
import QuantifiedNamed

namespace Fang.TptpCandidate.FullFof

inductive Binary where
  | conj | disj | implies | reverse | iff | xor | nand | nor
  deriving Repr, BEq, DecidableEq

def Binary.meaning : Binary → Prop → Prop → Prop
  | .conj, a, b => a ∧ b
  | .disj, a, b => a ∨ b
  | .implies, a, b => a → b
  | .reverse, a, b => b → a
  | .iff, a, b => a ↔ b
  | .xor, a, b => ¬ (a ↔ b)
  | .nand, a, b => ¬ (a ∧ b)
  | .nor, a, b => ¬ (a ∨ b)

def Binary.lower (operator : Binary) (a b : QuantifiedFOF.Formula) : QuantifiedFOF.Formula :=
  match operator with
  | .conj => .conj a b
  | .disj => .disj a b
  | .implies => .implies a b
  | .reverse => .implies b a
  | .iff => .conj (.implies a b) (.implies b a)
  | .xor => .neg (.conj (.implies a b) (.implies b a))
  | .nand => .neg (.conj a b)
  | .nor => .neg (.disj a b)

theorem binary_holds {D : Type} (model : Interpretation D) (valuation : Nat → D)
    (operator : Binary) (left right : QuantifiedFOF.Formula) :
    (operator.lower left right).Holds model valuation ↔
      operator.meaning (left.Holds model valuation) (right.Holds model valuation) := by
  cases operator <;> simp [Binary.lower, Binary.meaning, QuantifiedFOF.Formula.Holds, iff_def]

inductive Formula where
  | atom : String → List Source.Term → Formula
  | equal : Source.Term → Source.Term → Formula
  | truth | falsity
  | neg : Formula → Formula
  | pair : Binary → Formula → Formula → Formula
  | all : String → Formula → Formula
  | ex : String → Formula → Formula
  deriving Repr

def Formula.Holds {D : Type} (model : Source.Interpretation D) (valuation : String → D) : Formula → Prop
  | .atom name args => model.predicate name (args.map (Source.Term.eval model valuation))
  | .equal left right => left.eval model valuation = right.eval model valuation
  | .truth => True
  | .falsity => False
  | .neg body => ¬ body.Holds model valuation
  | .pair operator left right => operator.meaning (left.Holds model valuation) (right.Holds model valuation)
  | .all name body => ∀ value, body.Holds model (NamedQuantified.update valuation name value)
  | .ex name body => ∃ value, body.Holds model (NamedQuantified.update valuation name value)

def Formula.Within (bound : List String) : Formula → Prop
  | .atom _ args => ∀ arg ∈ args, NamedQuantified.TermWithin bound arg
  | .equal left right => NamedQuantified.TermWithin bound left ∧ NamedQuantified.TermWithin bound right
  | .truth | .falsity => True
  | .neg body => body.Within bound
  | .pair _ left right => left.Within bound ∧ right.Within bound
  | .all name body | .ex name body => body.Within (name :: bound)

def Formula.functions : Formula → List Arity.Symbol
  | .atom _ args => args.flatMap Arity.termFunctions
  | .equal left right => Arity.termFunctions left ++ Arity.termFunctions right
  | .truth | .falsity => []
  | .neg body | .all _ body | .ex _ body => body.functions
  | .pair _ left right => left.functions ++ right.functions

def Formula.predicates : Formula → List Arity.Symbol
  | .atom name args => [(name, args.length)]
  | .equal _ _ | .truth | .falsity => []
  | .neg body | .all _ body | .ex _ body => body.predicates
  | .pair _ left right => left.predicates ++ right.predicates

/-- Binder occurrences enter the table even when unused. Repeated spellings
    share their source ID; lexical scope still lives in the formula tree. -/
def Formula.variableNames : Formula → List String
  | .atom _ args => args.flatMap Arity.termVariables
  | .equal left right => Arity.termVariables left ++ Arity.termVariables right
  | .truth | .falsity => []
  | .neg body => body.variableNames
  | .pair _ left right => left.variableNames ++ right.variableNames
  | .all name body | .ex name body => name :: body.variableNames

def Formula.variableTable (formula : Formula) : Arity.Table :=
  Arity.collect [] (formula.variableNames.map (fun name => (name, 0)))

def Formula.variables (formula : Formula) : Source.Variables where
  id := fun name => Arity.id formula.variableTable (name, 0)
  name := fun index => (formula.variableTable[index]?.getD ("", 0)).1

theorem variable_roundtrip (formula : Formula) {name : String}
    (member : name ∈ formula.variableNames) :
    formula.variables.name (formula.variables.id name) = name := by
  have present : (name, 0) ∈ formula.variableTable :=
    (Arity.collect_mem [] _ _).mpr (Or.inr (List.mem_map.mpr ⟨name, member, rfl⟩))
  simp only [Formula.variables, Arity.id_roundtrip present, Option.getD_some]

def Formula.encode (functions predicates : Arity.Table) (variables : Source.Variables) :
    Formula → QuantifiedFOF.Formula
  | .atom name args => .atom ⟨Arity.id predicates (name, args.length), args.map (Arity.encodeTerm functions variables)⟩
  | .equal left right => .atom ⟨predicates.length,
      [Arity.encodeTerm functions variables left, Arity.encodeTerm functions variables right]⟩
  | .truth => .truth
  | .falsity => .falsity
  | .neg body => .neg (body.encode functions predicates variables)
  | .pair operator left right => operator.lower (left.encode functions predicates variables)
      (right.encode functions predicates variables)
  | .all name body => .all (variables.id name) (body.encode functions predicates variables)
  | .ex name body => .ex (variables.id name) (body.encode functions predicates variables)

/-- Mathematical equality occupies the slot immediately after all ordinary
    source predicates. The complete original table determines that slot. -/
def reserve {D : Type} (reserved : Nat) (model : Interpretation D) : Interpretation D where
  function := model.function
  predicate := fun id args => if id = reserved then
    match args with | [left, right] => left = right | _ => False
    else model.predicate id args

def toNumeric {D : Type} (model : Source.Interpretation D)
    (functions predicates : Arity.Table) : Interpretation D :=
  reserve predicates.length (Arity.toNumeric model functions predicates)

end Fang.TptpCandidate.FullFof
