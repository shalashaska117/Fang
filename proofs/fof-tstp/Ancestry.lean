/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license. -/
import Fang.FOF.TstpExport

namespace Fang.FofTstpExport

/-- The generic builder guard from proofs/tstp/Acceptance.lean, stated here
    without importing its CNF-only parser correspondence dependencies. -/
private theorem trace_checked {problem : TstpExport.NamedProblem}
    {certificate : Certificate} {output : TstpExport.Export}
    (built : TstpExport.build problem certificate = .ok output) :
    check (preprocess problem.signature.problem) certificate = true := by
  by_cases length : certificate.steps.length > 1000
  · simp [TstpExport.build, length, bind, Except.bind, pure, Except.pure, throw] at built
  by_cases wellFormed : certificateWellFormed problem.signature certificate = true
  · by_cases checked : check (preprocess problem.signature.problem) certificate = true
    · exact checked
    · simp [TstpExport.build, length, wellFormed, checked, bind, Except.bind, pure, Except.pure, throw] at built
  · simp [TstpExport.build, length, wellFormed, bind, Except.bind, pure, Except.pure, throw] at built

def LeafOrigin (declarations : List GroundFOF.Declaration) (names : List String)
    (start : Nat) (leaf : Leaf) : Prop :=
  ∃ offset, leaf.declaration = start + offset ∧
    declarations[offset]? = some leaf.body ∧ names[offset]? = some leaf.sourceName ∧
    leaf.body.clauses[leaf.localClause]? = some leaf.clause ∧
    leaf.rawName = (match leaf.body with
      | .cnf _ => leaf.sourceName
      | .fof _ => leafName leaf.declaration leaf.localClause)

theorem declarationLeaves_origin {body : GroundFOF.Declaration} {index : Nat}
    {name : String} {leaf : Leaf} (member : leaf ∈ declarationLeaves body index name) :
    leaf.body = body ∧ leaf.declaration = index ∧ leaf.sourceName = name ∧
    leaf.body.clauses[leaf.localClause]? = some leaf.clause ∧
    leaf.rawName = (match leaf.body with
      | .cnf _ => leaf.sourceName
      | .fof _ => leafName leaf.declaration leaf.localClause) := by
  obtain ⟨⟨clause, position⟩, atPosition, same⟩ := List.mem_map.mp member
  have atPosition := List.mk_mem_zipIdx_iff_getElem?.mp atPosition
  cases same
  exact ⟨rfl, rfl, rfl, atPosition, rfl⟩

theorem collectLeaves_origin {declarations : List GroundFOF.Declaration}
    {names : List String} {start : Nat} {output : List Leaf}
    (collected : collectLeaves declarations names start = .ok output)
    {leaf : Leaf} (member : leaf ∈ output) : LeafOrigin declarations names start leaf := by
  induction declarations generalizing names start output with
  | nil =>
    cases names <;> simp [collectLeaves, pure, Except.pure, throw] at collected
    subst output
    cases member
  | cons body rest ih =>
    cases names with
    | nil => simp [collectLeaves, throw] at collected
    | cons name names =>
      by_cases valid : Frontend.lowerName name = true
      · cases tailEq : collectLeaves rest names (start + 1) with
        | error error =>
          simp [collectLeaves, valid, tailEq, bind, Except.bind] at collected
        | ok tail =>
          have shape : declarationLeaves body start name ++ tail = output := by
            simpa [collectLeaves, valid, tailEq, bind, Except.bind, pure, Except.pure] using collected
          rw [← shape] at member
          rcases List.mem_append.mp member with first | later
          · obtain ⟨bodyEq, indexEq, nameEq, clauseAt, rawName⟩ := declarationLeaves_origin first
            exact ⟨0, by simpa using indexEq, by simp [bodyEq], by simp [nameEq], clauseAt, rawName⟩
          · obtain ⟨offset, indexEq, bodyAt, nameAt, clauseAt, rawName⟩ := ih tailEq later
            exact ⟨offset + 1, by omega, by simpa using bodyAt, by simpa using nameAt, clauseAt, rawName⟩
      · simp [collectLeaves, valid, bind, Except.bind, throw] at collected

theorem leaves_origin {decoded : FOFFrontend.Decoded} {output : List Leaf}
    (collected : leaves decoded = .ok output) {leaf : Leaf} (member : leaf ∈ output) :
    decoded.declarations[leaf.declaration]? = some leaf.body ∧
    decoded.state.clauseNames[leaf.declaration]? = some leaf.sourceName ∧
    leaf.body.clauses[leaf.localClause]? = some leaf.clause := by
  obtain ⟨offset, indexEq, bodyAt, nameAt, clauseAt, _⟩ := collectLeaves_origin collected member
  simp only [Nat.zero_add] at indexEq
  simpa only [indexEq] using And.intro bodyAt (And.intro nameAt clauseAt)

theorem build_source {decoded : FOFFrontend.Decoded} {certificate : Certificate} {output : Export}
    (built : build decoded certificate = .ok output) :
    output.decoded = decoded ∧ leaves decoded = .ok output.leaves := by
  unfold build at built
  cases leafEq : leaves decoded with
  | error error => simp [leafEq, bind, Except.bind] at built
  | ok items =>
    simp only [leafEq, bind, Except.bind] at built
    split at built
    · contradiction
    · split at built
      · contradiction
      · cases built
        exact ⟨rfl, rfl⟩

theorem build_checked {decoded : FOFFrontend.Decoded} {certificate : Certificate} {output : Export}
    (built : build decoded certificate = .ok output) :
    check (GroundFOF.prepareDeclarations decoded.declarations) certificate = true := by
  unfold build at built
  cases leafEq : leaves decoded with
  | error error => simp [leafEq, bind, Except.bind] at built
  | ok items =>
    simp only [leafEq, bind, Except.bind] at built
    split at built
    · contradiction
    · split at built
      · contradiction
      · rename_i trace traceEq
        exact trace_checked traceEq

theorem export_original_unsat {input proof fileLabel text : String}
    (exported : exportText input proof fileLabel = .ok text) :
    ¬ FOFGrammar.BytesSatisfiable (Source.Grammar.spelling input) := by
  cases decodedEq : FOFFrontend.decode input with
  | error error => simp [exportText, decodedEq, bind, Except.bind] at exported
  | ok decoded =>
    cases certEq : FOFVersioned.decodeCertificate proof with
    | error error => simp [exportText, decodedEq, certEq, bind, Except.bind] at exported
    | ok certificate =>
      cases buildEq : build decoded certificate with
      | error error => simp [exportText, decodedEq, certEq, buildEq, bind, Except.bind] at exported
      | ok output =>
        exact FOFFrontend.decode_check_original_unsat decodedEq certificate (build_checked buildEq)

/-- This is the semantic obligation behind a `status(thm)` clausification row.
    It applies to one declared local clause, before literal deduplication. -/
theorem clausification_consequence {D : Type} (model : Interpretation D)
    (declaration : GroundFOF.Declaration) (clause : Clause)
    (origin : clause ∈ declaration.clauses)
    (source : declaration.Models model) : clause.Valid model :=
  ((GroundFOF.declaration_models model declaration).mpr source) clause origin

theorem indexed_clausification_consequence {D : Type} (model : Interpretation D)
    (declaration : GroundFOF.Declaration) (index : Nat) (clause : Clause)
    (origin : declaration.clauses[index]? = some clause)
    (source : declaration.Models model) : clause.Valid model :=
  clausification_consequence model declaration clause (List.mem_of_getElem? origin) source

theorem original_declaration_consequence {D : Type} (model : Interpretation D)
    (declarations : List GroundFOF.Declaration) (declarationIndex clauseIndex : Nat)
    (declaration : GroundFOF.Declaration) (clause : Clause)
    (sourceAt : declarations[declarationIndex]? = some declaration)
    (clauseAt : declaration.clauses[clauseIndex]? = some clause)
    (original : GroundFOF.DeclarationsModels model declarations) : clause.Valid model :=
  indexed_clausification_consequence model declaration clauseIndex clause clauseAt
    (original declaration (List.mem_of_getElem? sourceAt))

/-- Successful construction retains a checked source position for every leaf.
    This does not yet establish correspondence of the printed TSTP rows. -/
theorem build_leaf_consequence {D : Type} (model : Interpretation D)
    {decoded : FOFFrontend.Decoded} {certificate : Certificate} {output : Export}
    (built : build decoded certificate = .ok output) {leaf : Leaf}
    (member : leaf ∈ output.leaves)
    (original : GroundFOF.DeclarationsModels model decoded.declarations) :
    leaf.clause.Valid model := by
  have collected := (build_source built).2
  obtain ⟨sourceAt, _, clauseAt⟩ := leaves_origin collected member
  exact original_declaration_consequence model decoded.declarations
    leaf.declaration leaf.localClause leaf.body leaf.clause sourceAt clauseAt original

end Fang.FofTstpExport
