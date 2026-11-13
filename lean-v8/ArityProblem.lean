/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import AritySemantics

namespace Fang.TptpCandidate.Arity

def clauseFunctions (clause : Source.Clause) : List Symbol :=
  clause.literals.flatMap (fun literal => literal.arguments.flatMap termFunctions)

def clausePredicates (clause : Source.Clause) : List Symbol :=
  clause.literals.map (fun literal => (literal.predicate, literal.arguments.length))

def clauseVariables (clause : Source.Clause) : Table :=
  collect [] (clause.literals.flatMap (fun literal =>
    literal.arguments.flatMap (fun term => (termVariables term).map (fun name => (name, 0)))))

def variables (clause : Source.Clause) : Source.Variables where
  id := fun name => id (clauseVariables clause) (name, 0)
  name := fun index => ((clauseVariables clause)[index]?.getD ("", 0)).1

def functionTable (problem : Source.Problem) : Table := collect [] (problem.flatMap clauseFunctions)
def predicateTable (problem : Source.Problem) : Table := collect [] (problem.flatMap clausePredicates)

def encodeClause (functions predicates : Table) (clause : Source.Clause) : Fang.Clause :=
  clause.literals.map (encodeLiteral functions predicates (variables clause))

def encodeProblem (problem : Source.Problem) : Fang.Problem :=
  problem.map (encodeClause (functionTable problem) (predicateTable problem))

theorem collected_literal_covered {problem : Source.Problem} {clause : Source.Clause}
    (member : clause ∈ problem) {literal : Source.Literal} (present : literal ∈ clause.literals) :
    LiteralCovered (functionTable problem) (predicateTable problem) literal := by
  constructor
  · apply (collect_mem [] _ _).mpr
    right
    exact List.mem_flatMap.mpr ⟨clause, member, List.mem_map.mpr ⟨literal, present, rfl⟩⟩
  · intro term termMember symbol occurrence
    apply (collect_mem [] _ _).mpr
    right
    exact List.mem_flatMap.mpr ⟨clause, member,
      List.mem_flatMap.mpr ⟨literal, present, List.mem_flatMap.mpr ⟨term, termMember, occurrence⟩⟩⟩

theorem clause_variables_covered {clause : Source.Clause} {literal : Source.Literal}
    (present : literal ∈ clause.literals) {term : Source.Term} (member : term ∈ literal.arguments) :
    VariablesCovered (variables clause) term := by
  intro name occurrence
  have found : (name, 0) ∈ clauseVariables clause := by
    apply (collect_mem [] _ _).mpr
    right
    exact List.mem_flatMap.mpr ⟨literal, present, List.mem_flatMap.mpr
      ⟨term, member, List.mem_map.mpr ⟨name, occurrence, rfl⟩⟩⟩
  simp only [variables, id_roundtrip found, Option.getD_some]

theorem clause_valid_toNumeric {problem : Source.Problem} {clause : Source.Clause}
    (member : clause ∈ problem) {D : Type} (model : Source.Interpretation D)
    (valid : clause.Valid model) :
    (encodeClause (functionTable problem) (predicateTable problem) clause).Valid
      (toNumeric model (functionTable problem) (predicateTable problem)) := by
  intro valuation
  obtain ⟨literal, present, holds⟩ := valid (fun name => valuation ((variables clause).id name))
  refine ⟨encodeLiteral (functionTable problem) (predicateTable problem) (variables clause) literal,
    List.mem_map.mpr ⟨literal, present, rfl⟩, ?_⟩
  exact (literal_holds_toNumeric literal _ _ _ (collected_literal_covered member present) model valuation).mpr holds

theorem clause_valid_toNamed (functions predicates : Table) (clause : Source.Clause)
    {D : Type} (model : Fang.Interpretation D)
    (valid : (encodeClause functions predicates clause).Valid model) :
    clause.Valid (toNamed model functions predicates) := by
  intro valuation
  obtain ⟨encoded, present, holds⟩ := valid (fun index => valuation ((variables clause).name index))
  obtain ⟨literal, member, rfl⟩ := List.mem_map.mp present
  refine ⟨literal, member, ?_⟩
  exact (literal_holds_toNamed literal functions predicates (variables clause)
    (fun _ occurrence => clause_variables_covered member occurrence) model valuation).mpr holds

theorem problem_models_toNumeric (problem : Source.Problem) {D : Type}
    (model : Source.Interpretation D) (models : problem.Models model) :
    (encodeProblem problem).Models (toNumeric model (functionTable problem) (predicateTable problem)) := by
  intro clause member
  obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
  exact clause_valid_toNumeric present model (models source present)

theorem problem_models_toNamed (problem : Source.Problem) {D : Type}
    (model : Fang.Interpretation D) (models : (encodeProblem problem).Models model) :
    problem.Models (toNamed model (functionTable problem) (predicateTable problem)) := by
  intro clause member
  apply clause_valid_toNamed _ _ clause model
  exact models _ (List.mem_map.mpr ⟨clause, member, rfl⟩)

theorem problem_satisfiable_iff (problem : Source.Problem) :
    Source.Satisfiable problem ↔ Fang.Satisfiable (encodeProblem problem) := by
  constructor
  · rintro ⟨domain, inhabited, model, models⟩
    exact ⟨domain, inhabited, toNumeric model (functionTable problem) (predicateTable problem),
      problem_models_toNumeric problem model models⟩
  · rintro ⟨domain, inhabited, model, models⟩
    exact ⟨domain, inhabited, toNamed model (functionTable problem) (predicateTable problem),
      problem_models_toNamed problem model models⟩

theorem complete_original_function_bound {problem : Source.Problem} {symbol : Symbol}
    (member : symbol ∈ problem.flatMap clauseFunctions) :
    id (functionTable problem) symbol < (functionTable problem).length :=
  original_ids_below_fresh _ member

theorem complete_original_predicate_bound {problem : Source.Problem} {symbol : Symbol}
    (member : symbol ∈ problem.flatMap clausePredicates) :
    id (predicateTable problem) symbol < (predicateTable problem).length :=
  original_ids_below_fresh _ member

end Fang.TptpCandidate.Arity
