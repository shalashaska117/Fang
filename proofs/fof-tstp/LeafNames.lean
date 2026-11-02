/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Unchecked proof draft over the actual exporter naming functions.
   No exporter definition or executable naming algorithm is replaced here. -/
import Fang.FOF.TstpExport
import Names
import Fang.FOF.TSTP.Ancestry

namespace Fang.FofTstpExport
open TstpExport.BuilderProof

theorem leaf_name_chars (declaration localClause : Nat) :
    (leafName declaration localClause).toList =
      ['f', 'a', 'n', 'g', ':', 'c', 'l', 'a', 'u', 's', 'i', 'f', 'y', ':'] ++
        (declaration.repr.toList ++ ':' :: localClause.repr.toList) := by
  simp only [leafName, String.toList_append, List.append_assoc]
  rfl

private theorem decimal_no_colon (value : Nat) :
    ∀ character ∈ value.repr.toList, character ≠ ':' := by
  intro character member same
  have member : character ∈ Nat.toDigits 10 value := by simpa only [Nat.toList_repr] using member
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) member
  subst character
  simp [Char.isDigit] at digit

private theorem colon_split_unique (left right : List Char) (leftTail rightTail : List Char)
    (leftNoColon : ∀ c ∈ left, c ≠ ':') (rightNoColon : ∀ c ∈ right, c ≠ ':')
    (equal : left ++ ':' :: leftTail = right ++ ':' :: rightTail) :
    left = right ∧ leftTail = rightTail := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => exact ⟨rfl, (List.cons.inj equal).2⟩
    | cons first rest =>
      exact False.elim (rightNoColon first List.mem_cons_self (List.cons.inj equal).1.symm)
  | cons first rest ih =>
    cases right with
    | nil => exact False.elim (leftNoColon first List.mem_cons_self (List.cons.inj equal).1)
    | cons other restRight =>
      obtain ⟨rfl, tails⟩ := List.cons.inj equal
      obtain ⟨rfl, same⟩ := ih restRight
        (fun c member => leftNoColon c (List.mem_cons_of_mem _ member))
        (fun c member => rightNoColon c (List.mem_cons_of_mem _ member)) tails
      exact ⟨rfl, same⟩

theorem leaf_name_injective {leftDeclaration rightDeclaration leftClause rightClause : Nat}
    (equal : leafName leftDeclaration leftClause = leafName rightDeclaration rightClause) :
    leftDeclaration = rightDeclaration ∧ leftClause = rightClause := by
  have chars := congrArg String.toList equal
  have suffix : leftDeclaration.repr.toList ++ ':' :: leftClause.repr.toList =
      rightDeclaration.repr.toList ++ ':' :: rightClause.repr.toList := by
    simpa [leaf_name_chars] using chars
  obtain ⟨first, second⟩ := colon_split_unique _ _ _ _
    (decimal_no_colon leftDeclaration) (decimal_no_colon rightDeclaration) suffix
  constructor
  · exact decimal_name_injective (String.toList_inj.mp first)
  · exact decimal_name_injective (String.toList_inj.mp second)

theorem leaf_name_not_lower (declaration localClause : Nat) :
    Frontend.lowerName (leafName declaration localClause) = false := by
  rw [Frontend.lowerName, leaf_name_chars]
  rfl

theorem source_leaf_distinct (name : String) (declaration localClause : Nat)
    (valid : Frontend.lowerName name = true) : name ≠ leafName declaration localClause := by
  intro equal
  rw [equal, leaf_name_not_lower] at valid
  contradiction

theorem leaf_generated_distinct (declaration localClause : Nat) (kind : NameKind) (node : Nat) :
    leafName declaration localClause ≠ generatedName kind node := by
  intro equal
  have tag := congrArg (fun name : String => name.toList[5]?) equal
  cases kind <;> simp [leaf_name_chars, generated_name_chars, prefixChars] at tag

private theorem zipIdx_index_lower (clauses : List Clause) (start : Nat) {entry : Clause × Nat}
    (member : entry ∈ clauses.zipIdx start) : start ≤ entry.2 := by
  induction clauses generalizing start with
  | nil => simp at member
  | cons clause clauses ih =>
    have shape : entry = (clause, start) ∨ entry ∈ clauses.zipIdx (start + 1) := by
      simpa using member
    rcases shape with rfl | later
    · exact Nat.le_refl _
    · have bound := ih (start + 1) later
      omega

private theorem indexed_leaf_names_nodup (clauses : List Clause) (declaration start : Nat) :
    ((clauses.zipIdx start).map (fun entry => leafName declaration entry.2)).Nodup := by
  induction clauses generalizing start with
  | nil => simp
  | cons clause clauses ih =>
    have fresh : leafName declaration start ∉
        (clauses.zipIdx (start + 1)).map (fun entry => leafName declaration entry.2) := by
      intro member
      obtain ⟨entry, indexed, same⟩ := List.mem_map.mp member
      have equal := (leaf_name_injective same).2
      have bound := zipIdx_index_lower clauses (start + 1) indexed
      omega
    simpa using List.nodup_cons.mpr ⟨fresh, ih (start + 1)⟩

theorem declarationLeaves_names_nodup (body : GroundFOF.Declaration) (declaration : Nat)
    (sourceName : String) : ((declarationLeaves body declaration sourceName).map Leaf.rawName).Nodup := by
  cases body with
  | cnf clause => simp [declarationLeaves, GroundFOF.Declaration.clauses]
  | fof formula =>
    simpa [declarationLeaves, GroundFOF.Declaration.clauses, List.map_map, Function.comp_def]
      using indexed_leaf_names_nodup formula.clausify declaration 0

theorem collectLeaves_lower_sources {declarations : List GroundFOF.Declaration}
    {names : List String} {start : Nat} {output : List Leaf}
    (collected : collectLeaves declarations names start = .ok output) : LowerNames names := by
  induction declarations generalizing names start output with
  | nil =>
    cases names with
    | nil => simp [LowerNames]
    | cons name names => simp [collectLeaves, throw] at collected
  | cons body rest ih =>
    cases names with
    | nil => simp [collectLeaves, throw] at collected
    | cons name names =>
      by_cases valid : Frontend.lowerName name = true
      · cases tailEq : collectLeaves rest names (start + 1) with
        | error error => simp [collectLeaves, valid, tailEq, bind, Except.bind] at collected
        | ok tail =>
          have remaining := ih tailEq
          intro source member
          rcases List.mem_cons.mp member with same | member
          · simpa only [same] using valid
          · exact remaining source member
      · simp [collectLeaves, valid, bind, Except.bind, throw] at collected

/-- This is the generated-name disjointness needed by the generalized builder.
    It deliberately makes no LowerNames claim about generated clausification leaves. -/
theorem collectLeaves_generated_disjoint {declarations : List GroundFOF.Declaration}
    {names : List String} {start : Nat} {output : List Leaf}
    (collected : collectLeaves declarations names start = .ok output) :
    ∀ name ∈ output.map Leaf.rawName, ∀ kind node, name ≠ generatedName kind node := by
  intro raw member kind node
  obtain ⟨leaf, leafMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨offset, indexEq, bodyAt, nameAt, clauseAt, rawName⟩ := collectLeaves_origin collected leafMember
  have nameMember : leaf.sourceName ∈ names := List.mem_iff_getElem?.mpr ⟨offset, nameAt⟩
  have valid := collectLeaves_lower_sources collected leaf.sourceName nameMember
  cases bodyEq : leaf.body with
  | cnf clause =>
    have raw : leaf.rawName = leaf.sourceName := by simpa only [bodyEq] using rawName
    rw [raw]
    exact source_generated_distinct _ _ _ valid
  | fof formula =>
    have raw : leaf.rawName = leafName leaf.declaration leaf.localClause := by
      simpa only [bodyEq] using rawName
    rw [raw]
    exact leaf_generated_distinct _ _ _ _

theorem collectLeaves_names_nodup {declarations : List GroundFOF.Declaration}
    {names : List String} {start : Nat} {output : List Leaf}
    (unique : names.Nodup) (collected : collectLeaves declarations names start = .ok output) :
    (output.map Leaf.rawName).Nodup := by
  induction declarations generalizing names start output with
  | nil =>
    cases names <;> simp [collectLeaves, pure, Except.pure, throw] at collected
    subst output
    simp
  | cons body rest ih =>
    cases names with
    | nil => simp [collectLeaves, throw] at collected
    | cons name names =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
      by_cases valid : Frontend.lowerName name = true
      · cases tailEq : collectLeaves rest names (start + 1) with
        | error error => simp [collectLeaves, valid, tailEq, bind, Except.bind] at collected
        | ok tail =>
          have shape : declarationLeaves body start name ++ tail = output := by
            simpa [collectLeaves, valid, tailEq, bind, Except.bind, pure, Except.pure] using collected
          rw [← shape, List.map_append]
          apply List.nodup_append.mpr
          refine ⟨declarationLeaves_names_nodup body start name, ih unique tailEq, ?_⟩
          intro first firstMem later laterMem collision
          obtain ⟨firstLeaf, firstLeafMember, rfl⟩ := List.mem_map.mp firstMem
          obtain ⟨laterLeaf, laterLeafMember, rfl⟩ := List.mem_map.mp laterMem
          obtain ⟨firstBody, firstIndex, firstName, _, firstRaw⟩ := declarationLeaves_origin firstLeafMember
          obtain ⟨offset, laterIndex, _, laterName, _, laterRaw⟩ := collectLeaves_origin tailEq laterLeafMember
          have laterMember : laterLeaf.sourceName ∈ names := List.mem_iff_getElem?.mpr ⟨offset, laterName⟩
          have laterValid := collectLeaves_lower_sources tailEq laterLeaf.sourceName laterMember
          cases body with
          | cnf clause =>
            have firstEq : firstLeaf.rawName = name := by simpa only [firstBody, firstName] using firstRaw
            cases laterBody : laterLeaf.body with
            | cnf laterClause =>
              have laterEq : laterLeaf.rawName = laterLeaf.sourceName := by simpa only [laterBody] using laterRaw
              have same : name = laterLeaf.sourceName := firstEq.symm.trans (collision.trans laterEq)
              exact absent (same.symm ▸ laterMember)
            | fof formula =>
              have laterEq : laterLeaf.rawName = leafName laterLeaf.declaration laterLeaf.localClause := by
                simpa only [laterBody] using laterRaw
              exact source_leaf_distinct name _ _ valid (firstEq.symm.trans (collision.trans laterEq))
          | fof formula =>
            have firstEq : firstLeaf.rawName = leafName start firstLeaf.localClause := by
              simpa only [firstBody, firstIndex] using firstRaw
            cases laterBody : laterLeaf.body with
            | cnf laterClause =>
              have laterEq : laterLeaf.rawName = laterLeaf.sourceName := by simpa only [laterBody] using laterRaw
              exact source_leaf_distinct laterLeaf.sourceName _ _ laterValid
                (laterEq.symm.trans (collision.symm.trans firstEq))
            | fof laterFormula =>
              have laterEq : laterLeaf.rawName = leafName laterLeaf.declaration laterLeaf.localClause := by
                simpa only [laterBody] using laterRaw
              have same := (leaf_name_injective (firstEq.symm.trans (collision.trans laterEq))).1
              omega
      · simp [collectLeaves, valid, bind, Except.bind, throw] at collected

end Fang.FofTstpExport
