/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The actual named encoder constructs the semantic name/ID witness. -/
import EqualitySourceEncoding
import Fang.FrontendNames

namespace Fang.EqualityFrontend.Encoding
open EqualitySource

theorem names_roundtrip {entries : List String} {name : String} (member : name ∈ entries) :
    namesValue entries (namesId entries name) = name := by
  cases found : Frontend.namedIndex name entries 0 with
  | none => exact False.elim ((Frontend.namedIndex_none_iff _ _ _).mp found member)
  | some id =>
    obtain ⟨within, same, _⟩ := (Frontend.namedIndex_first_iff _ _ _).mp found
    simp [namesValue, namesId, found, List.getElem?_eq_getElem within, same]

theorem symbol_roundtrip {entries : List (String × Nat)} {entry : String × Nat}
    (member : entry ∈ entries) : namesValue (names entries) (namesId (names entries) entry.1) = entry.1 := by
  apply names_roundtrip
  simp only [names, List.mem_eraseDups, List.mem_map]
  exact ⟨entry, member, rfl⟩

theorem consistent_spec {entries : List (String × Nat)} (checked : consistent entries = true) :
    ∀ entry ∈ entries, firstArity entries entry.1 = some entry.2 := by
  simpa only [consistent, List.all_eq_true, beq_iff_eq] using checked

mutual
theorem term_encoding (term : Source.Term) (signature : Source.Signature)
    (symbols : Source.Symbols) (variables : Source.Variables)
    (functions : ∀ entry ∈ termFunctions term,
      symbols.functionName (symbols.functionId entry.1) = entry.1 ∧
      signature.functionArity entry.1 = some entry.2)
    (variableNames : ∀ name ∈ termVariables term, variables.name (variables.id name) = name) :
    Source.TermEncoding signature symbols variables term (encodeTerm symbols variables term) := by
  cases term with
  | var name =>
    simp only [encodeTerm]
    exact .var name (variableNames name (by simp [termVariables]))
  | app name arguments =>
    simp only [encodeTerm]
    have root := functions (name, arguments.length) (by simp [termFunctions])
    apply Source.TermEncoding.app name arguments _ root.1 root.2
    apply terms_encoding arguments signature symbols variables
    · intro entry member
      exact functions entry (by simp only [termFunctions, List.mem_cons]; exact .inr member)
    · simpa only [termVariables] using variableNames

theorem terms_encoding (terms : List Source.Term) (signature : Source.Signature)
    (symbols : Source.Symbols) (variables : Source.Variables)
    (functions : ∀ entry ∈ terms.flatMap termFunctions,
      symbols.functionName (symbols.functionId entry.1) = entry.1 ∧
      signature.functionArity entry.1 = some entry.2)
    (variableNames : ∀ name ∈ terms.flatMap termVariables, variables.name (variables.id name) = name) :
    Source.TermsEncoding signature symbols variables terms (terms.map (encodeTerm symbols variables)) := by
  cases terms with
  | nil => exact .nil
  | cons term rest =>
    apply Source.TermsEncoding.cons
    · apply term_encoding term signature symbols variables
      · intro entry member
        exact functions entry (by simp only [List.flatMap_cons, List.mem_append]; exact .inl member)
      · intro name member
        exact variableNames name (by simp only [List.flatMap_cons, List.mem_append]; exact .inl member)
    · apply terms_encoding rest signature symbols variables
      · intro entry member
        exact functions entry (by simp only [List.flatMap_cons, List.mem_append]; exact .inr member)
      · intro name member
        exact variableNames name (by simp only [List.flatMap_cons, List.mem_append]; exact .inr member)
end

theorem atom_encoding (atom : EqualitySource.Atom) (signature : Source.Signature)
    (symbols : Source.Symbols) (variables : Source.Variables)
    (functions : ∀ entry ∈ atomFunctions atom,
      symbols.functionName (symbols.functionId entry.1) = entry.1 ∧
      signature.functionArity entry.1 = some entry.2)
    (predicates : ∀ entry ∈ atomPredicates atom,
      symbols.predicateName (symbols.predicateId entry.1) = entry.1 ∧
      signature.predicateArity entry.1 = some entry.2)
    (variableNames : ∀ name ∈ atomVariables atom, variables.name (variables.id name) = name) :
    AtomEncoding signature symbols variables atom (encodeAtom symbols variables atom) := by
  cases atom with
  | predicate name arguments =>
    have root := predicates (name, arguments.length) (by simp [atomPredicates])
    exact .predicate name arguments _ root.1 root.2
      (terms_encoding arguments signature symbols variables functions variableNames)
  | equal left right =>
    apply AtomEncoding.equal
    · apply term_encoding left signature symbols variables
      · intro entry member
        exact functions entry (List.mem_append_left _ member)
      · intro name member
        exact variableNames name (List.mem_append_left _ member)
    · apply term_encoding right signature symbols variables
      · intro entry member
        exact functions entry (List.mem_append_right _ member)
      · intro name member
        exact variableNames name (List.mem_append_right _ member)

theorem related_map {α β : Type} (relation : α → β → Prop) (function : α → β)
    (items : List α) (each : ∀ item ∈ items, relation item (function item)) :
    Source.RelatedLists relation items (items.map function) := by
  induction items with
  | nil => exact .nil
  | cons item rest ih =>
    exact .cons (each item List.mem_cons_self)
      (ih (fun value member => each value (List.mem_cons_of_mem _ member)))

theorem clause_encoding (clause : EqualitySource.Clause) (functionEntries predicateEntries : List (String × Nat))
    (functions : ∀ entry ∈ clauseFunctions clause, entry ∈ functionEntries)
    (predicates : ∀ entry ∈ clausePredicates clause, entry ∈ predicateEntries)
    (functionArities : consistent functionEntries = true)
    (predicateArities : consistent predicateEntries = true) :
    ClauseEncoding (signature functionEntries predicateEntries) (symbols functionEntries predicateEntries)
      (variables clause) clause (encodeClause (symbols functionEntries predicateEntries) clause) := by
  apply related_map
  intro literal member
  refine ⟨rfl, ?_⟩
  apply atom_encoding
  · intro entry within
    have present := functions entry (List.mem_flatMap.mpr ⟨literal, member, within⟩)
    exact ⟨symbol_roundtrip present, consistent_spec functionArities entry present⟩
  · intro entry within
    have present := predicates entry (List.mem_flatMap.mpr ⟨literal, member, within⟩)
    exact ⟨symbol_roundtrip present, consistent_spec predicateArities entry present⟩
  · intro name within
    apply names_roundtrip
    simp only [clauseVariables, List.mem_eraseDups]
    exact List.mem_flatMap.mpr ⟨literal, member, within⟩

theorem problem_encoding (named : EqualitySource.Problem) (uniqueNames : (named.map EqualitySource.Clause.name).Nodup)
    (functionArities : consistent (named.flatMap clauseFunctions) = true)
    (predicateArities : consistent (named.flatMap clausePredicates) = true) :
    ProblemEncoding (signature (named.flatMap clauseFunctions) (named.flatMap clausePredicates))
      (symbols (named.flatMap clauseFunctions) (named.flatMap clausePredicates)) named
      (named.map (encodeClause (symbols (named.flatMap clauseFunctions) (named.flatMap clausePredicates)))) := by
  refine ⟨uniqueNames, ?_⟩
  apply related_map
  intro clause member
  refine ⟨variables clause, clause_encoding clause _ _ ?_ ?_ functionArities predicateArities⟩
  · intro entry within
    exact List.mem_flatMap.mpr ⟨clause, member, within⟩
  · intro entry within
    exact List.mem_flatMap.mpr ⟨clause, member, within⟩

theorem encode_sound {named : EqualitySource.Problem} {encoded : Encoded} (success : encode named = .ok encoded) :
    ∃ signature symbols, ProblemEncoding signature symbols named encoded.problem := by
  unfold encode at success
  dsimp only at success
  split at success
  · cases success
  · rename_i unique
    have uniqueNames : (named.map EqualitySource.Clause.name).Nodup := by simpa using unique
    split at success
    · cases success
    · rename_i functions
      have functionArities : consistent (named.flatMap clauseFunctions) = true := by simpa using functions
      split at success
      · cases success
      · rename_i predicates
        have predicateArities : consistent (named.flatMap clausePredicates) = true := by simpa using predicates
        cases Except.ok.inj success
        exact ⟨_, _, problem_encoding named uniqueNames functionArities predicateArities⟩

end Fang.EqualityFrontend.Encoding
