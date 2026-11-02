/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Actual numeric construction supplies the reserved-head semantic encoding. -/
import EqualityQuantifiedEncoding
import EqualityEncodingProof

namespace Fang.QuantifiedEqualityFrontend.Encoding
open NamedQuantifiedEquality
open EqualityFrontend.Encoding (names namesId namesValue signature symbols consistent
  symbolTable names_roundtrip symbol_roundtrip consistent_spec term_encoding terms_encoding
  termFunctions termVariables related_map)

theorem names_id_bound {entries : List String} {name : String} (member : name ∈ entries) :
    namesId entries name < entries.length := by
  cases found : Frontend.namedIndex name entries 0 with
  | none => exact False.elim ((Frontend.namedIndex_none_iff _ _ _).mp found member)
  | some id =>
    obtain ⟨within, _, _⟩ := (Frontend.namedIndex_first_iff _ _ _).mp found
    simpa [namesId, found] using within

theorem symbol_id_bound {entries : List (String × Nat)} {entry : String × Nat}
    (member : entry ∈ entries) : namesId (names entries) entry.1 < (names entries).length := by
  apply names_id_bound
  simp only [names, List.mem_eraseDups, List.mem_map]
  exact ⟨entry, member, rfl⟩

theorem atom_encoding (atom : NamedQuantifiedEquality.Atom) (reserved : Nat)
    (signature : Source.Signature) (symbols : Source.Symbols) (variables : Source.Variables)
    (functions : ∀ entry ∈ atomFunctions atom,
      symbols.functionName (symbols.functionId entry.1) = entry.1 ∧
      signature.functionArity entry.1 = some entry.2)
    (predicates : ∀ entry ∈ atomPredicates atom,
      symbols.predicateName (symbols.predicateId entry.1) = entry.1 ∧
      signature.predicateArity entry.1 = some entry.2 ∧ symbols.predicateId entry.1 < reserved)
    (variableNames : ∀ name ∈ atomVariables atom, variables.name (variables.id name) = name) :
    AtomEncoding reserved signature symbols variables atom (encodeAtom reserved symbols variables atom) := by
  cases atom with
  | predicate name arguments =>
    have root := predicates (name, arguments.length) (by simp [atomPredicates])
    exact .predicate name arguments _ root.1 root.2.1 root.2.2
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

theorem formula_encoding (formula : Formula) (reserved : Nat)
    (signature : Source.Signature) (symbols : Source.Symbols) (variables : Source.Variables)
    (functions : ∀ entry ∈ formulaFunctions formula,
      symbols.functionName (symbols.functionId entry.1) = entry.1 ∧
      signature.functionArity entry.1 = some entry.2)
    (predicates : ∀ entry ∈ formulaPredicates formula,
      symbols.predicateName (symbols.predicateId entry.1) = entry.1 ∧
      signature.predicateArity entry.1 = some entry.2 ∧ symbols.predicateId entry.1 < reserved)
    (variableNames : ∀ name ∈ formulaVariables formula, variables.name (variables.id name) = name) :
    NamedQuantifiedEquality.Encoding reserved signature symbols variables formula
      (encodeFormula reserved symbols variables formula) := by
  induction formula with
  | atom value => exact .atom (atom_encoding value reserved signature symbols variables functions predicates variableNames)
  | truth => exact .truth
  | falsity => exact .falsity
  | neg body ih => exact .neg (ih functions predicates variableNames)
  | conj left right il ir | disj left right il ir | implies left right il ir =>
    have first := il
      (fun entry member => functions entry (List.mem_append_left _ member))
      (fun entry member => predicates entry (List.mem_append_left _ member))
      (fun name member => variableNames name (List.mem_append_left _ member))
    have second := ir
      (fun entry member => functions entry (List.mem_append_right _ member))
      (fun entry member => predicates entry (List.mem_append_right _ member))
      (fun name member => variableNames name (List.mem_append_right _ member))
    first | exact .conj first second | exact .disj first second | exact .implies first second
  | all name body ih =>
    exact .all name (variableNames name List.mem_cons_self)
      (ih functions predicates (fun variableName member => variableNames variableName (List.mem_cons_of_mem _ member)))
  | ex name body ih =>
    exact .ex name (variableNames name List.mem_cons_self)
      (ih functions predicates (fun variableName member => variableNames variableName (List.mem_cons_of_mem _ member)))

structure LiteralEncoding (reserved : Nat) (signature : Source.Signature) (symbols : Source.Symbols)
    (variables : Source.Variables) (named : EqualitySource.Literal) (encoded : Fang.Literal) : Prop where
  polarity : named.positive = encoded.positive
  atom : AtomEncoding reserved signature symbols variables (sourceAtom named.atom) encoded.atom

inductive DeclarationEncoding (reserved : Nat) (signature : Source.Signature) (symbols : Source.Symbols) :
    Declaration → EncodedDeclaration → Prop where
  | cnf {named : EqualitySource.Clause} {encoded : Fang.Clause} (variables : Source.Variables)
      (literals : Source.RelatedLists (LiteralEncoding reserved signature symbols variables) named.literals encoded) :
      DeclarationEncoding reserved signature symbols (.cnf named) (.cnf named.name encoded)
  | fof {name named encoded} (variables : Source.Variables)
      (body : NamedQuantifiedEquality.Encoding reserved signature symbols variables named encoded) :
      DeclarationEncoding reserved signature symbols (.fof name named) (.fof name encoded)

theorem declaration_encoding (declaration : Declaration) (functionEntries predicateEntries : List (String × Nat))
    (functions : ∀ entry ∈ declarationFunctions declaration, entry ∈ functionEntries)
    (predicates : ∀ entry ∈ declarationPredicates declaration, entry ∈ predicateEntries)
    (functionArities : consistent functionEntries = true)
    (predicateArities : consistent predicateEntries = true) :
    DeclarationEncoding (names predicateEntries).length (signature functionEntries predicateEntries)
      (symbols functionEntries predicateEntries) declaration
      (encodeDeclaration (names predicateEntries).length (symbols functionEntries predicateEntries) declaration) := by
  cases declaration with
  | cnf clause =>
    apply DeclarationEncoding.cnf (variables (.cnf clause))
    apply related_map
    intro literal member
    refine ⟨rfl, ?_⟩
    apply atom_encoding
    · intro entry within
      have same : atomFunctions (sourceAtom literal.atom) = EqualityFrontend.Encoding.atomFunctions literal.atom := by
        cases literal.atom <;> rfl
      rw [same] at within
      have present := functions entry (List.mem_flatMap.mpr ⟨literal, member, within⟩)
      exact ⟨symbol_roundtrip present, consistent_spec functionArities entry present⟩
    · intro entry within
      have same : atomPredicates (sourceAtom literal.atom) = EqualityFrontend.Encoding.atomPredicates literal.atom := by
        cases literal.atom <;> rfl
      rw [same] at within
      have present := predicates entry (List.mem_flatMap.mpr ⟨literal, member, within⟩)
      exact ⟨symbol_roundtrip present, consistent_spec predicateArities entry present, symbol_id_bound present⟩
    · intro name within
      apply names_roundtrip
      change name ∈ (EqualityFrontend.Encoding.clauseVariables clause)
      simp only [EqualityFrontend.Encoding.clauseVariables, List.mem_eraseDups]
      have same : atomVariables (sourceAtom literal.atom) = EqualityFrontend.Encoding.atomVariables literal.atom := by
        cases literal.atom <;> rfl
      rw [same] at within
      exact List.mem_flatMap.mpr ⟨literal, member, within⟩
  | fof name body =>
    apply DeclarationEncoding.fof (variables (.fof name body))
    apply formula_encoding
    · intro entry member
      have present := functions entry member
      exact ⟨symbol_roundtrip present, consistent_spec functionArities entry present⟩
    · intro entry member
      have present := predicates entry member
      exact ⟨symbol_roundtrip present, consistent_spec predicateArities entry present, symbol_id_bound present⟩
    · intro variableName member
      apply names_roundtrip
      simpa only [declarationVariables, List.mem_eraseDups] using member

theorem encode_sound {named : List Declaration} {encoded : Encoded} (success : encode named = .ok encoded) :
    ∃ signature symbols, Source.RelatedLists (DeclarationEncoding encoded.equalityId signature symbols)
      named encoded.declarations := by
  unfold encode at success
  dsimp only at success
  split at success
  · cases success
  · split at success
    · cases success
    · rename_i functions
      have functionArities : consistent (named.flatMap declarationFunctions) = true := by simpa using functions
      split at success
      · cases success
      · rename_i predicates
        have predicateArities : consistent (named.flatMap declarationPredicates) = true := by simpa using predicates
        cases Except.ok.inj success
        refine ⟨signature (named.flatMap declarationFunctions) (named.flatMap declarationPredicates),
          symbols (named.flatMap declarationFunctions) (named.flatMap declarationPredicates), ?_⟩
        apply related_map
        intro declaration member
        apply declaration_encoding declaration _ _ _ _ functionArities predicateArities
        · intro entry within
          exact List.mem_flatMap.mpr ⟨declaration, member, within⟩
        · intro entry within
          exact List.mem_flatMap.mpr ⟨declaration, member, within⟩

theorem encode_reserved_slot {named : List Declaration} {encoded : Encoded}
    (success : encode named = .ok encoded) :
    encoded.equalityId = encoded.originalPredicates.length ∧
    encoded.predicateArities = encoded.originalPredicates.map Prod.snd ++ [2] := by
  unfold encode at success
  dsimp only at success
  split at success
  · cases success
  · split at success
    · cases success
    · split at success
      · cases success
      · cases Except.ok.inj success
        simp [symbolTable]

end Fang.QuantifiedEqualityFrontend.Encoding
