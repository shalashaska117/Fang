/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed role tasks over sealed include bundles: a role-aware record decoder, a role-aware framer whose role-free view is the axiom-only bundle framer, roles read after include expansion, and the signed bundle meanings with distinct-object separation. -/
import NumericTask
import CoverageFramerPremises

namespace Fang.TptpCandidate.Roles.Bundle
open FullFof Numeric

/-! The role-aware record decoder. -/

namespace RoleByte

/-- The record decoder the framer calls, with roles: the accepted role decoder, unchanged. -/
def declaration (seen : List Name) (endOffset : Nat) (tokens : List FullFof.Token) :
    Except Error (Bytes.Entry × List FullFof.Token) :=
  Bytes.declaration seen endOffset tokens

/-- Soundness in the form of `CnfBoolean.declaration_sound`, for the role grammar. -/
theorem declaration_sound {seen endOffset tokens value final}
    (success : declaration seen endOffset tokens = .ok (value, final)) :
    Bytes.DeclarationTokens tokens value final ∧ value.original.name ∉ seen :=
  Bytes.declaration_sound success

/-- The original record is an accepted `CnfBoolean.declaration` result on the same tokens with only the role kind replaced, so every accepted record lemma applies to it. -/
theorem declaration_original {seen endOffset tokens value final}
    (success : declaration seen endOffset tokens = .ok (value, final)) :
    ∃ header : Bytes.Header, tokens = header.tokens ∧
      CnfBoolean.declaration seen endOffset header.patched = .ok (value.original, final) := by
  obtain ⟨header, shape, _, _, original, _, _⟩ := Bytes.declaration_witness success
  exact ⟨header, shape, original⟩

theorem grammar_keyword {tokens original rest}
    (grammar : CnfBoolean.DeclarationTokens tokens original rest) :
    ∃ keyword more, tokens = keyword :: more ∧
      keyword.kind = .legacy (.lower (FullFof.Grammar.BodyKind original.body)) := by
  cases grammar with
  | declaration keywordKind => exact ⟨_, _, rfl, keywordKind⟩

/-- A decoded conjecture has an FOF body: the decoder rejects the `cnf` keyword for a conjecture. -/
theorem declaration_goal_fof {seen endOffset tokens value final}
    (success : declaration seen endOffset tokens = .ok (value, final))
    (goal : value.role = .conjecture) : ∃ formula, value.original.body = .fof formula := by
  obtain ⟨header, _, _, valid, originalAt, _, _⟩ := Bytes.declaration_witness success
  obtain ⟨keyword, more, shape, kind⟩ := grammar_keyword (CnfBoolean.declaration_sound originalAt).1
  simp only [Bytes.Header.patched, List.cons.injEq] at shape
  obtain ⟨rfl, -⟩ := shape
  simp only [Bytes.invalidGoal, goal, decide_true, Bool.true_and] at valid
  cases bodyShape : value.original.body with
  | fof formula => exact ⟨formula, rfl⟩
  | cnf literals =>
    rw [bodyShape] at kind
    rw [kind] at valid
    simp only [FullFof.Grammar.BodyKind] at valid
    exact absurd valid (by decide)

end RoleByte

/-! The role-aware framer. Every step except the record decoder is the framer's own definition. -/

inductive RoleStatement where
  | formula : Bytes.Entry → RoleStatement
  | directive : List String → Coverage.Selection → RoleStatement

structure RoleFile where
  key : Coverage.Key
  statements : List RoleStatement

abbrev RoleBundle := List RoleFile

def RoleStatement.forget : RoleStatement → Coverage.Statement
  | .formula entry => .formula entry.original
  | .directive parts selection => .directive parts selection

/-- The role-free view: the same files, keys and statement positions. -/
def forget (bundle : RoleBundle) : Coverage.Bundle :=
  bundle.map fun file => ⟨file.key, file.statements.map RoleStatement.forget⟩

/-- `Framer.formulaRecord` with `RoleByte.declaration` in place of `CnfBoolean.declaration`. -/
def formulaRecord (seen : List Name) (endOffset : Nat) (pieces : List Coverage.Framer.Piece) :
    Except Error Bytes.Entry :=
  match Coverage.Framer.nameGuard pieces with
  | .error problem => .error problem
  | .ok () =>
    match RoleByte.declaration seen endOffset ((Coverage.Framer.cutRecord pieces).1.map Coverage.Framer.coreToken) with
    | .error problem => .error problem
    | .ok (value, rest) =>
      if !rest.isEmpty then .error ⟨.invalid, (rest.head?.map FullFof.Token.start).getD endOffset⟩
      else if !Coverage.Framer.objectsWellUsed value.original then .error ⟨.invalid, value.original.start⟩
      else match (Coverage.Framer.cutRecord pieces).2 with
        | none => .ok value
        | some annotationPieces => match Coverage.Framer.annotation annotationPieces with
          | .error problem => .error problem
          | .ok () => .ok value

/-- `Framer.statements` over role statements. -/
def statements : Nat → List Name → Nat → List Coverage.Framer.Piece → Except Error (List RoleStatement)
  | 0, _, endOffset, _ => .error ⟨.resource, endOffset⟩
  | _ + 1, _, _, [] => .ok []
  | fuel + 1, seen, endOffset, first :: more =>
    if seen.length ≥ 1000 then .error ⟨.resource, first.start⟩
    else
      let split := Coverage.Framer.splitStatement 0 [] (first :: more)
      match Coverage.Framer.keyword split.1 with
      | some "include" =>
        match Coverage.Framer.directive split.1 with
        | .error problem => .error problem
        | .ok (parts, selection) =>
          match statements fuel seen endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.directive parts selection :: tail)
      | some "tpi" => .error ⟨.unsupported, first.start⟩
      | _ =>
        match formulaRecord seen endOffset split.1 with
        | .error problem => .error problem
        | .ok value =>
          match statements fuel (value.original.name :: seen) endOffset split.2 with
          | .error problem => .error problem
          | .ok tail => .ok (.formula value :: tail)

def frameFile (bytes : List UInt8) (maximum : Nat) : Except Error (List RoleStatement) :=
  match Coverage.Framer.tokenize bytes maximum with
  | .error problem => .error problem
  | .ok pieces => statements (pieces.length + 1) [] bytes.length pieces

def frameBundle : List (Coverage.Key × List UInt8) → Nat → Except Error RoleBundle
  | [], _ => .ok []
  | (key, bytes) :: rest, maximum =>
    match frameFile bytes maximum with
    | .error problem => .error problem
    | .ok framed => match frameBundle rest maximum with
      | .error problem => .error problem
      | .ok others => .ok (⟨key, framed⟩ :: others)

/-! Soundness of the role-aware framer, following `CoverageFramerSound`. -/

def RoleDecoded (value : Bytes.Entry) : Prop :=
  ∃ seen endOffset tokens, RoleByte.declaration seen endOffset tokens = .ok (value, []) ∧
    Coverage.Framer.objectsWellUsed value.original = true

theorem formulaRecord_sound {seen : List Name} {endOffset : Nat} {pieces : List Coverage.Framer.Piece}
    {value : Bytes.Entry} (success : formulaRecord seen endOffset pieces = .ok value) : RoleDecoded value := by
  cases guard : Coverage.Framer.nameGuard pieces with
  | error problem => simp [formulaRecord, guard] at success
  | ok done =>
    cases decoded : RoleByte.declaration seen endOffset
        ((Coverage.Framer.cutRecord pieces).1.map Coverage.Framer.coreToken) with
    | error problem => simp [formulaRecord, guard, decoded] at success
    | ok pair =>
      obtain ⟨found, rest⟩ := pair
      by_cases empty : rest.isEmpty = true
      · by_cases used : Coverage.Framer.objectsWellUsed found.original = true
        · have same : found = value := by
            cases annotationAt : (Coverage.Framer.cutRecord pieces).2 with
            | none =>
              simp [formulaRecord, guard, decoded, empty, used, annotationAt] at success
              exact success
            | some annotationPieces =>
              cases annotated : Coverage.Framer.annotation annotationPieces with
              | error problem =>
                simp [formulaRecord, guard, decoded, empty, used, annotationAt, annotated] at success
              | ok finished =>
                simp [formulaRecord, guard, decoded, empty, used, annotationAt, annotated] at success
                exact success
          subst same
          have restNil : rest = [] := List.isEmpty_iff.mp empty
          subst restNil
          exact ⟨seen, endOffset, _, decoded, used⟩
        · simp [formulaRecord, guard, decoded, empty, used] at success
      · simp [formulaRecord, guard, decoded, empty] at success

theorem statements_sound : ∀ fuel seen endOffset pieces result,
    statements fuel seen endOffset pieces = .ok result →
      ∀ value, RoleStatement.formula value ∈ result → RoleDecoded value := by
  intro fuel
  induction fuel with
  | zero => intro seen endOffset pieces result success; simp [statements] at success
  | succ fuel ih =>
    intro seen endOffset pieces result success value member
    cases pieces with
    | nil =>
      simp only [statements, Except.ok.injEq] at success
      subst success
      simp at member
    | cons first more =>
      simp only [statements] at success
      split at success
      · cases success
      · split at success
        · split at success
          · cases success
          · split at success
            · cases success
            · rename_i tail later
              simp only [Except.ok.injEq] at success
              subst success
              rcases List.mem_cons.mp member with same | inTail
              · cases same
              · exact ih _ _ _ _ later value inTail
        · cases success
        · split at success
          · cases success
          · rename_i found recorded
            split at success
            · cases success
            · rename_i tail later
              simp only [Except.ok.injEq] at success
              subst success
              rcases List.mem_cons.mp member with same | inTail
              · cases same
                exact formulaRecord_sound recorded
              · exact ih _ _ _ _ later value inTail

theorem frameFile_sound {bytes : List UInt8} {maximum : Nat} {result : List RoleStatement}
    (success : frameFile bytes maximum = .ok result) {value : Bytes.Entry}
    (member : RoleStatement.formula value ∈ result) : RoleDecoded value := by
  unfold frameFile at success
  split at success
  · cases success
  · exact statements_sound _ _ _ _ _ success value member

theorem frameBundle_sound {files : List (Coverage.Key × List UInt8)} {maximum : Nat} {bundle : RoleBundle}
    (success : frameBundle files maximum = .ok bundle) :
    ∀ file ∈ bundle, ∀ value, RoleStatement.formula value ∈ file.statements → RoleDecoded value := by
  induction files generalizing bundle with
  | nil => simp only [frameBundle, Except.ok.injEq] at success; subst success; simp
  | cons first rest ih =>
    obtain ⟨key, bytes⟩ := first
    simp only [frameBundle] at success
    split at success
    · cases success
    · rename_i framed framedAt
      split at success
      · cases success
      · rename_i others tail
        simp only [Except.ok.injEq] at success
        subst success
        intro file member value present
        rcases List.mem_cons.mp member with same | later
        · subst same
          exact frameFile_sound framedAt present
        · exact ih tail file later value present

/-! Roles are read after include expansion, at the expanded items only. -/

def roleStatementAt (bundle : RoleBundle) (item : Coverage.Item) : Option RoleStatement := do
  let file ← bundle[item.1]?
  file.statements[item.2]?

theorem forget_statementAt (bundle : RoleBundle) (item : Coverage.Item) :
    Coverage.statementAt (forget bundle) item = (roleStatementAt bundle item).map RoleStatement.forget := by
  simp only [Coverage.statementAt, roleStatementAt, forget, List.getElem?_map]
  cases bundle[item.1]? with
  | none => rfl
  | some file => simp [List.getElem?_map]

/-- The expanded entries in expansion order; an unselected record never appears. -/
def entriesOf (bundle : RoleBundle) (items : List Coverage.Item) : List Bytes.Entry :=
  items.filterMap fun item => match roleStatementAt bundle item with
    | some (.formula value) => some value
    | _ => none

theorem entriesOf_original (bundle : RoleBundle) (items : List Coverage.Item) :
    (entriesOf bundle items).map Bytes.Entry.original = Coverage.declarationsOf (forget bundle) items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [entriesOf, Coverage.declarationsOf, List.filterMap_cons, forget_statementAt] at ih ⊢
    cases found : roleStatementAt bundle item with
    | none => simpa using ih
    | some statement =>
      cases statement with
      | formula value => simp [RoleStatement.forget, ih]
      | directive parts selection => simpa [RoleStatement.forget] using ih

/-- Each original goal with its bundle identity (file index, statement index). -/
def goalItems (bundle : RoleBundle) (items : List Coverage.Item) : List (Coverage.Item × Bytes.Entry) :=
  (items.filterMap fun item => match roleStatementAt bundle item with
    | some (.formula value) => some (item, value)
    | _ => none).filter fun pair => decide (pair.2.role = .conjecture)

theorem goalItems_entries (bundle : RoleBundle) (items : List Coverage.Item) :
    (goalItems bundle items).map Prod.snd =
      (entriesOf bundle items).filter fun value => decide (value.role = .conjecture) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [goalItems, entriesOf, List.filterMap_cons] at ih ⊢
    cases found : roleStatementAt bundle item with
    | none => simpa using ih
    | some statement =>
      cases statement with
      | formula value =>
        by_cases goal : value.role = .conjecture
        · simp [goal, ih]
        · simp [goal, ih]
      | directive parts selection => simpa using ih

theorem framed_entries_sound {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle files maximum = .ok bundle) (items : List Coverage.Item)
    {value : Bytes.Entry} (member : value ∈ entriesOf bundle items) : RoleDecoded value := by
  simp only [entriesOf, List.mem_filterMap] at member
  obtain ⟨item, _, found⟩ := member
  cases at_item : roleStatementAt bundle item with
  | none => simp [at_item] at found
  | some statement =>
    cases statement with
    | directive parts selection => simp [at_item] at found
    | formula decoded =>
      simp only [at_item, Option.some.injEq] at found
      subst found
      simp only [roleStatementAt, bind, Option.bind] at at_item
      cases fileAt : bundle[item.1]? with
      | none => simp [fileAt] at at_item
      | some file =>
        simp only [fileAt] at at_item
        exact frameBundle_sound framed file (List.mem_of_getElem? fileAt) decoded
          (List.mem_of_getElem? at_item)

/-- The original part of every expanded entry is an accepted `CnfBoolean.declaration` record (the framer's `Decoded`). -/
theorem framed_entries_decoded {files : List (Coverage.Key × List UInt8)} {maximum : Nat}
    {bundle : RoleBundle} (framed : frameBundle files maximum = .ok bundle) (items : List Coverage.Item)
    {value : Bytes.Entry} (member : value ∈ entriesOf bundle items) : Coverage.Framer.Decoded value.original := by
  obtain ⟨seen, endOffset, tokens, decoded, used⟩ := framed_entries_sound framed items member
  obtain ⟨header, _, original⟩ := RoleByte.declaration_original decoded
  exact ⟨seen, endOffset, header.patched, original, used⟩

theorem framed_closed {files : List (Coverage.Key × List UInt8)} {maximum : Nat} {bundle : RoleBundle}
    (framed : frameBundle files maximum = .ok bundle) (items : List Coverage.Item) :
    Bytes.Closed (entriesOf bundle items) := by
  intro value member
  obtain ⟨seen, endOffset, tokens, decoded, _⟩ := framed_entries_sound framed items member
  exact Bytes.declaration_closed decoded

theorem framed_goals_fof {files : List (Coverage.Key × List UInt8)} {maximum : Nat} {bundle : RoleBundle}
    (framed : frameBundle files maximum = .ok bundle) (items : List Coverage.Item)
    {value : Bytes.Entry} (member : value ∈ entriesOf bundle items) (goal : value.role = .conjecture) :
    ∃ formula, value.original.body = .fof formula := by
  obtain ⟨seen, endOffset, tokens, decoded, _⟩ := framed_entries_sound framed items member
  exact RoleByte.declaration_goal_fof decoded goal

/-- Every distinct object of the expanded declarations is a nullary entry of the complete tables, following `framed_objects_covered`. -/
theorem framed_objects_covered {files : List (Coverage.Key × List UInt8)} {maximum : Nat} {bundle : RoleBundle}
    (framed : frameBundle files maximum = .ok bundle) (items : List Coverage.Item)
    {input : Integration.NumericInput}
    (encoded : Integration.readInput (Coverage.declarationsOf (forget bundle) items) = some input) :
    ∀ label ∈ Coverage.Framer.objectNames (Coverage.declarationsOf (forget bundle) items),
      (label, 0) ∈ input.functions := by
  intro label member
  rw [(Integration.readInput_tables encoded).1]
  simp only [Coverage.Framer.objectNames, List.mem_eraseDups, List.mem_filterMap, List.mem_flatMap] at member
  obtain ⟨symbol, ⟨formula, formulaMember, present⟩, chosen⟩ := member
  by_cases object : Coverage.Framer.isObject symbol.1 = true
  · simp only [object, ↓reduceIte, Option.some.injEq] at chosen
    subst chosen
    simp only [source, List.mem_map, Function.comp] at formulaMember
    obtain ⟨value, valueMember, rfl⟩ := formulaMember
    have entryMember : value ∈ (entriesOf bundle items).map Bytes.Entry.original := by
      rw [entriesOf_original]; exact valueMember
    obtain ⟨entry, entryAt, rfl⟩ := List.mem_map.mp entryMember
    obtain ⟨_, _, _, _, used⟩ := framed_entries_sound framed items entryAt
    have arity : symbol.2 = 0 := by
      simp only [Coverage.Framer.objectsWellUsed, Bool.and_eq_true, Bool.not_eq_true',
        List.any_eq_false] at used
      have := used.2 symbol present
      simp only [object, bne_iff_ne, ne_eq] at this
      exact Classical.byContradiction fun different => this ⟨trivial, different⟩
    have inSource : entry.original.body.formula ∈ source (Coverage.declarationsOf (forget bundle) items) :=
      List.mem_map.mpr ⟨entry.original, valueMember, rfl⟩
    have covered := (collected_covered inSource).functions symbol present
    have shape : symbol = (symbol.1, 0) := Prod.ext rfl arity
    rw [← shape]
    exact covered
  · simp [object] at chosen

/-! Signed bundle meanings. They keep `NamedSeparated` exactly as `Framer.ByteBundleSatisfiable` does. -/

/-- The bundle framed with roles, well shaped and expanded. -/
def Expanded (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) (bundle : RoleBundle)
    (items : List Coverage.Item) : Prop :=
  frameBundle files maximum = .ok bundle ∧ Coverage.Framer.wellShaped (forget bundle) fuel = true ∧
    Coverage.expand (forget bundle) fuel = .ok items

def objectsOf (bundle : RoleBundle) (items : List Coverage.Item) : List String :=
  Coverage.Framer.objectNames (Coverage.declarationsOf (forget bundle) items)

/-- One selected original conjecture, identified by its bundle item, follows from the selected premises in every model that keeps distinct objects apart. -/
def BundleGoalEntailed (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat)
    (item : Coverage.Item) : Prop :=
  ∃ bundle items entry, Expanded files maximum fuel bundle items ∧ (item, entry) ∈ goalItems bundle items ∧
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.Framer.NamedSeparated model (objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model entry.original.body.formula

/-- The statement for SZS Theorem over a bundle: at least one selected original conjecture, and every one is entailed. -/
def ByteBundleTheorem (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, Expanded files maximum fuel bundle items ∧ goalItems bundle items ≠ [] ∧
    ∀ pair ∈ goalItems bundle items, ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.Framer.NamedSeparated model (objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model pair.2.original.body.formula

/-- The signed counterpart of `Framer.ByteBundleSatisfiable` for a bundle without a selected conjecture: the positive inputs have a model that keeps distinct objects apart. -/
def ByteBundleInputsSatisfiable (files : List (Coverage.Key × List UInt8)) (maximum fuel : Nat) : Prop :=
  ∃ bundle items, Expanded files maximum fuel bundle items ∧ goalItems bundle items = [] ∧
    ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.Framer.NamedSeparated model (objectsOf bundle items) ∧
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.positiveInputs (Bytes.source (entriesOf bundle items))) model

theorem expanded_unique {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle other : RoleBundle} {items others : List Coverage.Item}
    (first : Expanded files maximum fuel bundle items) (second : Expanded files maximum fuel other others) :
    bundle = other ∧ items = others := by
  have same : bundle = other := Except.ok.inj (first.1.symm.trans second.1)
  subst same
  exact ⟨rfl, Except.ok.inj (first.2.2.symm.trans second.2.2)⟩

/-! Numeric refutations with the generated distinct-object axioms. -/

def objectIds (input : SignedInput) (bundle : RoleBundle) (items : List Coverage.Item) : List Nat :=
  (objectsOf bundle items).map fun label => Arity.id input.functions (label, 0)

/-- The generated disequalities as positive task items. -/
def distinctItems (input : SignedInput) (bundle : RoleBundle) (items : List Coverage.Item) : List SignedNumeric :=
  (Coverage.distinctAxioms input.predicates.length (objectIds input bundle items)).map positive

theorem read_tables {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    (read : readSigned (entriesOf bundle items) = some input) :
    Integration.readInput (Coverage.declarationsOf (forget bundle) items) =
      some ⟨input.functions, input.predicates, input.rows.map RoleRow.row⟩ := by
  rw [← entriesOf_original]
  exact (readSigned_exact read).1

theorem distinctItems_models {files : List (Coverage.Key × List UInt8)} {maximum : Nat} {bundle : RoleBundle}
    (framed : frameBundle files maximum = .ok bundle) {items : List Coverage.Item} {input : SignedInput}
    (read : readSigned (entriesOf bundle items) = some input)
    {D : Type} [Nonempty D] (model : Source.Interpretation D)
    (separated : Coverage.Framer.NamedSeparated model (objectsOf bundle items))
    (nodup : (objectIds input bundle items).Nodup) :
    TaskModels (FullFof.toNumeric model input.functions input.predicates) (distinctItems input bundle items) := by
  have covered := framed_objects_covered framed items (read_tables read)
  have agreement := model_toNumeric model input.functions input.predicates
  have numeric := (Coverage.Framer.separated_iff agreement covered).mp separated
  intro item member
  obtain ⟨declaration, present, rfl⟩ := List.mem_map.mp member
  rw [positive_holds]
  obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp present
  obtain ⟨left, right⟩ := pair
  obtain ⟨leftMember, rightMember, different⟩ := Coverage.pairs_mem pairMember
  apply (Coverage.disequality_models (Arity.toNumeric model input.functions input.predicates)
    input.predicates.length left right).mpr
  exact numeric left leftMember right rightMember (different nodup)

/-- One goal task, refuted together with the generated disequalities, proves that goal from the selected premises in every model that keeps distinct objects apart. -/
theorem goal_refuted_entails {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    {before after : List RoleRow} {goal : RoleRow} {task : List SignedNumeric}
    (expanded : Expanded files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (split : input.rows = before ++ goal :: after) (built : goalTask before goal after = some task)
    (nodup : (objectIds input bundle items).Nodup)
    (refuted : ¬ TaskSatisfiable input (task ++ distinctItems input bundle items)) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Coverage.Framer.NamedSeparated model (objectsOf bundle items) →
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source (entriesOf bundle items))) model →
        Bytes.sentence model goal.declaration.original := by
  intro D inhabited model separated premisesHold
  let _ : Nonempty D := inhabited
  apply Classical.byContradiction
  intro fails
  apply refuted
  refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
  rw [taskModels_append]
  exact ⟨(goalTask_models read (framed_closed expanded.1 items) split built (model_toNumeric model _ _)).mpr
      ⟨premisesHold, (Roles.negative_holds _ _).mpr fails⟩,
    distinctItems_models expanded.1 read model separated nodup⟩

theorem goalItems_member {bundle : RoleBundle} {items : List Coverage.Item}
    {pair : Coverage.Item × Bytes.Entry} (member : pair ∈ goalItems bundle items) :
    pair.2 ∈ entriesOf bundle items ∧ pair.2.role = .conjecture := by
  have mapped : pair.2 ∈ (goalItems bundle items).map Prod.snd := List.mem_map_of_mem member
  rw [goalItems_entries] at mapped
  simpa using mapped

/-- Theorem endpoint over a bundle: at least one selected conjecture, and every goal task refuted together with the generated disequalities. -/
theorem bundle_theorem_of_refuted {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    (expanded : Expanded files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (nonempty : goalItems bundle items ≠ [])
    (nodup : (objectIds input bundle items).Nodup)
    (refuted : ∀ split ∈ splits input.rows, split.2.1.role = .conjecture →
      ∃ task, goalTask split.1 split.2.1 split.2.2 = some task ∧
        ¬ TaskSatisfiable input (task ++ distinctItems input bundle items)) :
    ByteBundleTheorem files maximum fuel := by
  refine ⟨bundle, items, expanded, nonempty, ?_⟩
  intro pair member D inhabited model separated premisesHold
  obtain ⟨entryMember, role⟩ := goalItems_member member
  have inSource : (⟨pair.2.original.name, pair.2.role, pair.2.original.body.formula⟩ :
      Roles.Declaration Name FullFof.Formula) ∈ Bytes.source (entriesOf bundle items) :=
    List.mem_map_of_mem (f := fun value : Bytes.Entry =>
      (⟨value.original.name, value.role, value.original.body.formula⟩ : Roles.Declaration Name FullFof.Formula))
      entryMember
  obtain ⟨before, row, after, split, rowRole, same⟩ := goal_row read (Roles.goal_member.mpr ⟨inSource, role⟩)
  obtain ⟨task, built, unsat⟩ := refuted (before, row, after) (mem_splits.mpr split) rowRole
  have holds := goal_refuted_entails expanded read split built nodup unsat D inhabited model separated premisesHold
  rw [same] at holds
  exact holds

/-- The no-goal task, refuted together with the generated disequalities, shows that the bundle's positive inputs have no model keeping distinct objects apart. -/
theorem inputs_refuted_unsat {files : List (Coverage.Key × List UInt8)} {maximum fuel : Nat}
    {bundle : RoleBundle} {items : List Coverage.Item} {input : SignedInput}
    (expanded : Expanded files maximum fuel bundle items)
    (read : readSigned (entriesOf bundle items) = some input)
    (nodup : (objectIds input bundle items).Nodup)
    (refuted : ¬ TaskSatisfiable input (inputsTask input ++ distinctItems input bundle items)) :
    ¬ ByteBundleInputsSatisfiable files maximum fuel := by
  rintro ⟨other, others, otherExpanded, _, D, inhabited, model, separated, holds⟩
  obtain ⟨rfl, rfl⟩ := expanded_unique expanded otherExpanded
  let _ : Nonempty D := inhabited
  apply refuted
  refine ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates, ?_⟩
  rw [taskModels_append]
  exact ⟨(inputsTask_models read (framed_closed expanded.1 items) (model_toNumeric model _ _)).mpr holds,
    distinctItems_models expanded.1 read model separated nodup⟩

#print axioms Fang.TptpCandidate.Roles.Bundle.RoleByte.declaration_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.RoleByte.declaration_original
#print axioms Fang.TptpCandidate.Roles.Bundle.RoleByte.grammar_keyword
#print axioms Fang.TptpCandidate.Roles.Bundle.RoleByte.declaration_goal_fof
#print axioms Fang.TptpCandidate.Roles.Bundle.formulaRecord_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.statements_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.frameFile_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.frameBundle_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.forget_statementAt
#print axioms Fang.TptpCandidate.Roles.Bundle.entriesOf_original
#print axioms Fang.TptpCandidate.Roles.Bundle.goalItems_entries
#print axioms Fang.TptpCandidate.Roles.Bundle.framed_entries_sound
#print axioms Fang.TptpCandidate.Roles.Bundle.framed_entries_decoded
#print axioms Fang.TptpCandidate.Roles.Bundle.framed_closed
#print axioms Fang.TptpCandidate.Roles.Bundle.framed_goals_fof
#print axioms Fang.TptpCandidate.Roles.Bundle.framed_objects_covered
#print axioms Fang.TptpCandidate.Roles.Bundle.expanded_unique
#print axioms Fang.TptpCandidate.Roles.Bundle.read_tables
#print axioms Fang.TptpCandidate.Roles.Bundle.distinctItems_models
#print axioms Fang.TptpCandidate.Roles.Bundle.goal_refuted_entails
#print axioms Fang.TptpCandidate.Roles.Bundle.goalItems_member
#print axioms Fang.TptpCandidate.Roles.Bundle.bundle_theorem_of_refuted
#print axioms Fang.TptpCandidate.Roles.Bundle.inputs_refuted_unsat

end Fang.TptpCandidate.Roles.Bundle
