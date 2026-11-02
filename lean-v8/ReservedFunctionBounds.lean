/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import ReservedInput

namespace FangQuantifiedEqualityInput
open Fang Fang.QuantifiedEqualityFrontend Fang.QuantifiedCertificate FangQuantifiedPipeline
open Fang.QuantifiedFOF.Skolem

theorem encoded_term_below (term : Source.Term) (functions predicates : List (String × Nat))
    (variableMap : Source.Variables)
    (contained : ∀ entry ∈ EqualityFrontend.Encoding.termFunctions term, entry ∈ functions) :
    TermBelow (EqualityFrontend.Encoding.names functions).length
      (EqualityFrontend.Encoding.encodeTerm (EqualityFrontend.Encoding.symbols functions predicates) variableMap term) := by
  cases term with
  | var variableName => simp only [EqualityFrontend.Encoding.encodeTerm, TermBelow]
  | app functionName arguments =>
    simp only [EqualityFrontend.Encoding.encodeTerm, TermBelow]
    simp only [EqualityFrontend.Encoding.termFunctions] at contained
    refine ⟨Encoding.symbol_id_bound (contained (functionName, arguments.length) List.mem_cons_self), ?_⟩
    intro encoded member
    obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
    apply encoded_term_below child functions predicates variableMap
    intro entry within
    apply contained entry
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child, childMember, within⟩)
termination_by sizeOf term

theorem encoded_atom_below (atom : NamedQuantifiedEquality.Atom) (reserved : Nat)
    (functions predicates : List (String × Nat)) (variableMap : Source.Variables)
    (contained : ∀ entry ∈ Encoding.atomFunctions atom, entry ∈ functions) :
    ∀ term ∈ (Encoding.encodeAtom reserved (EqualityFrontend.Encoding.symbols functions predicates) variableMap atom).args,
      TermBelow (EqualityFrontend.Encoding.names functions).length term := by
  cases atom with
  | predicate predicateName arguments =>
    intro encoded member
    change encoded ∈ arguments.map (EqualityFrontend.Encoding.encodeTerm
      (EqualityFrontend.Encoding.symbols functions predicates) variableMap) at member
    obtain ⟨term, termMember, rfl⟩ := List.mem_map.mp member
    exact encoded_term_below term functions predicates variableMap (fun entry within =>
      contained entry (List.mem_flatMap.mpr ⟨term, termMember, within⟩))
  | equal left right =>
    intro encoded member
    simp only [Encoding.encodeAtom, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact encoded_term_below left functions predicates variableMap (fun entry within =>
        contained entry (List.mem_append_left _ within))
    · exact encoded_term_below right functions predicates variableMap (fun entry within =>
        contained entry (List.mem_append_right _ within))

theorem encoded_clause_below (clause : EqualitySource.Clause) (reserved : Nat)
    (functions predicates : List (String × Nat))
    (contained : ∀ entry ∈ EqualityFrontend.Encoding.clauseFunctions clause, entry ∈ functions) :
    ∀ literal ∈ clause.literals.map (Encoding.encodeLiteral reserved
      (EqualityFrontend.Encoding.symbols functions predicates) (Encoding.variables (.cnf clause))),
      ∀ term ∈ literal.atom.args, TermBelow (EqualityFrontend.Encoding.names functions).length term := by
  intro literal member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  apply encoded_atom_below (Encoding.sourceAtom original.atom) reserved functions predicates
  intro entry within
  apply contained entry
  apply List.mem_flatMap.mpr
  refine ⟨original, originalMember, ?_⟩
  have exactFunctions : Encoding.atomFunctions (Encoding.sourceAtom original.atom) =
      EqualityFrontend.Encoding.atomFunctions original.atom := by cases original.atom <;> rfl
  exact exactFunctions ▸ within

theorem encoded_retained_below (source : List NamedQuantifiedEquality.Declaration) (reserved : Nat)
    (functions predicates : List (String × Nat))
    (contained : ∀ declaration ∈ source, ∀ entry ∈ Encoding.declarationFunctions declaration, entry ∈ functions) :
    ProblemBelow (EqualityFrontend.Encoding.names functions).length
      (retained (numericDeclarations (source.map
        (Encoding.encodeDeclaration reserved (EqualityFrontend.Encoding.symbols functions predicates))))) := by
  induction source with
  | nil => simp [ProblemBelow, numericDeclarations, retained]
  | cons declaration rest ih =>
    have tail := ih (fun declaration member => contained declaration (List.mem_cons_of_mem _ member))
    cases declaration with
    | cnf clause =>
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact encoded_clause_below clause reserved functions predicates
          (contained (.cnf clause) List.mem_cons_self)
      · exact tail item member
    | fof sourceName body => exact tail

/-- The bound follows from the actual encoder's complete function inventory,
    including functions first encountered in later declarations. -/
theorem encoded_original_functions_below {named encoded}
    (success : Encoding.encode named = .ok encoded) :
    ProblemBelow encoded.functions.length (retained (numericDeclarations encoded.declarations)) := by
  unfold Encoding.encode at success
  dsimp only at success
  split at success
  · cases success
  · split at success
    · cases success
    · split at success
      · cases success
      · cases Except.ok.inj success
        simpa only [EqualityFrontend.Encoding.symbolTable, List.length_map] using
          encoded_retained_below named _ (named.flatMap Encoding.declarationFunctions)
            (named.flatMap Encoding.declarationPredicates)
            (fun declaration member entry within => List.mem_flatMap.mpr ⟨declaration, member, within⟩)

theorem prepareInput_retained_below {input maximum prepared}
    (success : prepareInput input maximum = .ok prepared) :
    ProblemBelow prepared.signature.functions.val.length
      (retained (numericDeclarations prepared.original.declarations)) := by
  obtain ⟨decoded, _⟩ := prepareInput_runs success
  obtain ⟨_, _, _, encoded⟩ := Fang.QuantifiedEqualityFrontend.decode_byte_encoding decoded
  have count : prepared.signature.functions.val.length = prepared.original.functions.length := by
    simpa only [List.length_map] using congrArg List.length (prepareInput_tables success).2.2.2.1
  rw [count]
  exact encoded_original_functions_below encoded

end FangQuantifiedEqualityInput
