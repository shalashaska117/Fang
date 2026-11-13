/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Every framed formula is a successful accepted-decoder record, and the
   named distinct-object reading meets the numeric generated axioms. -/
import CoverageFramer
import CoverageDistinct

namespace Fang.TptpCandidate.FullFof.Coverage.Framer

open Fang.TptpCandidate.FullFof.Coverage

/-- What the accepted decoder established for one framed record. -/
def Decoded (value : Declaration) : Prop :=
  ∃ seen endOffset tokens, CnfBoolean.declaration seen endOffset tokens = .ok (value, []) ∧
    objectsWellUsed value = true

theorem formulaRecord_sound {seen : List Name} {endOffset : Nat} {pieces : List Piece}
    {value : Declaration} (success : formulaRecord seen endOffset pieces = .ok value) : Decoded value := by
  cases guard : nameGuard pieces with
  | error failure => simp [formulaRecord, guard] at success
  | ok done =>
    cases decoded : CnfBoolean.declaration seen endOffset ((cutRecord pieces).1.map coreToken) with
    | error failure => simp [formulaRecord, guard, decoded] at success
    | ok pair =>
      obtain ⟨found, rest⟩ := pair
      by_cases empty : rest.isEmpty = true
      · by_cases used : objectsWellUsed found = true
        · have same : found = value := by
            cases annotationAt : (cutRecord pieces).2 with
            | none =>
              simp [formulaRecord, guard, decoded, empty, used, annotationAt] at success
              exact success
            | some annotationPieces =>
              cases annotated : annotation annotationPieces with
              | error failure =>
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
      ∀ value, Statement.formula value ∈ result → Decoded value := by
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

theorem frameFile_sound {bytes : List UInt8} {maximum : Nat} {result : List Statement}
    (success : frameFile bytes maximum = .ok result) {value : Declaration}
    (member : Statement.formula value ∈ result) : Decoded value := by
  unfold frameFile at success
  split at success
  · cases success
  · exact statements_sound _ _ _ _ _ success value member

theorem frameBundle_sound {files : List (Key × List UInt8)} {maximum : Nat} {bundle : Bundle}
    (success : frameBundle files maximum = .ok bundle) :
    ∀ file ∈ bundle, ∀ value, Statement.formula value ∈ file.statements → Decoded value := by
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

/-- Every expanded declaration of a framed bundle is an accepted record. -/
theorem framed_declarations_sound {files : List (Key × List UInt8)} {maximum : Nat}
    {bundle : Bundle} (framed : frameBundle files maximum = .ok bundle) (items : List Item)
    {value : Declaration} (member : value ∈ declarationsOf bundle items) : Decoded value := by
  simp only [declarationsOf, List.mem_filterMap] at member
  obtain ⟨item, _, found⟩ := member
  cases at_item : statementAt bundle item with
  | none => simp [at_item] at found
  | some statement =>
    cases statement with
    | directive parts selection => simp [at_item] at found
    | formula decoded =>
      simp only [at_item, Option.some.injEq] at found
      subst found
      simp only [statementAt, bind, Option.bind] at at_item
      cases fileAt : bundle[item.1]? with
      | none => simp [fileAt] at at_item
      | some file =>
        simp only [fileAt] at at_item
        exact frameBundle_sound framed file (List.mem_of_getElem? fileAt) decoded
          (List.mem_of_getElem? at_item)

/-- Composition with the accepted declaration grammar soundness. -/
theorem framed_declarations_grammar {files : List (Key × List UInt8)} {maximum : Nat}
    {bundle : Bundle} (framed : frameBundle files maximum = .ok bundle) (items : List Item)
    {value : Declaration} (member : value ∈ declarationsOf bundle items) :
    ∃ tokens, CnfBoolean.DeclarationTokens tokens value [] := by
  obtain ⟨seen, endOffset, tokens, decoded, _⟩ := framed_declarations_sound framed items member
  exact ⟨tokens, (CnfBoolean.declaration_sound decoded).1⟩

/-- The named and numeric distinctness conditions agree under any model
    agreement, for objects in the complete function table at arity zero. -/
theorem separated_iff {functions predicates : Arity.Table} {D : Type}
    {named : Source.Interpretation D} {numeric : Fang.Interpretation D}
    (agreement : ModelAgreement functions predicates named numeric) {names : List String}
    (covered : ∀ label ∈ names, (label, 0) ∈ functions) :
    NamedSeparated named names ↔
      Separated numeric (names.map fun label => Arity.id functions (label, 0)) := by
  have equation (label : String) (present : label ∈ names) :
      numeric.function (Arity.id functions (label, 0)) [] = named.function label [] :=
    agreement.function label [] (covered label present)
  constructor
  · intro separated left leftMember right rightMember distinct
    obtain ⟨first, firstMember, rfl⟩ := List.mem_map.mp leftMember
    obtain ⟨second, secondMember, rfl⟩ := List.mem_map.mp rightMember
    have different : first ≠ second := fun same => distinct (by rw [same])
    rw [equation first firstMember, equation second secondMember]
    exact separated first firstMember second secondMember different
  · intro separated first firstMember second secondMember different
    have ids : Arity.id functions (first, 0) ≠ Arity.id functions (second, 0) := fun same =>
      different (Prod.mk.inj (Arity.id_injective (covered first firstMember)
        (covered second secondMember) same)).1
    have apart := separated _ (List.mem_map_of_mem firstMember) _ (List.mem_map_of_mem secondMember) ids
    rw [equation first firstMember, equation second secondMember] at apart
    exact apart

/-- Named satisfiability with separated objects is the numeric
    distinct-object satisfiability over the accepted `readInput` tables. -/
theorem objects_distinct_satisfiable {values : List Declaration}
    {input : Integration.NumericInput} (encoded : Integration.readInput values = some input)
    (closed : Grammar.Closed values) {names : List String}
    (covered : ∀ label ∈ names, (label, 0) ∈ input.functions) :
    (∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
        Models (source values) model ∧ NamedSeparated model names) ↔
      DistinctSatisfiable input.predicates.length input.declarations
        (names.map fun label => Arity.id input.functions (label, 0)) := by
  constructor
  · rintro ⟨D, inhabited, named, holds, separated⟩
    have agreement := model_toNumeric named input.functions input.predicates
    exact ⟨D, inhabited, Arity.toNumeric named input.functions input.predicates,
      (separated_iff agreement covered).mp separated,
      (Integration.readInput_models encoded closed agreement).mpr holds⟩
  · rintro ⟨D, inhabited, model, separated, holds⟩
    have agreement := model_toNamed model input.functions input.predicates
    exact ⟨D, inhabited, Arity.toNamed model input.functions input.predicates,
      (Integration.readInput_models encoded closed agreement).mp holds,
      (separated_iff agreement covered).mpr separated⟩

/-- End to end: refuting the numeric problem with the generated pairwise
    disequalities refutes the sealed byte bundle. -/
theorem byte_bundle_generated_unsat {files : List (Key × List UInt8)} {maximum fuel : Nat}
    {bundle : Bundle} {items : List Item} {input : Integration.NumericInput}
    (framed : frameBundle files maximum = .ok bundle) (expanded : expand bundle fuel = .ok items)
    (encoded : Integration.readInput (declarationsOf bundle items) = some input)
    (closed : Grammar.Closed (declarationsOf bundle items))
    (covered : ∀ label ∈ objectNames (declarationsOf bundle items), (label, 0) ∈ input.functions)
    (nodup : ((objectNames (declarationsOf bundle items)).map
      fun label => Arity.id input.functions (label, 0)).Nodup)
    (refuted : ¬ ReservedSatisfiable input.predicates.length
      (input.declarations ++ distinctAxioms input.predicates.length
        ((objectNames (declarationsOf bundle items)).map fun label => Arity.id input.functions (label, 0)))) :
    ¬ ByteBundleSatisfiable files maximum fuel := by
  apply byte_bundle_unsat framed expanded
  intro D inhabited model holds separated
  exact distinct_unsat _ _ nodup refuted
    ((objects_distinct_satisfiable encoded closed covered).mp ⟨D, inhabited, model, holds, separated⟩)

#print axioms Fang.TptpCandidate.FullFof.Coverage.Framer.formulaRecord_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.Framer.statements_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.Framer.frameFile_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.Framer.frameBundle_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.Framer.framed_declarations_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.Framer.framed_declarations_grammar
#print axioms Fang.TptpCandidate.FullFof.Coverage.Framer.separated_iff
#print axioms Fang.TptpCandidate.FullFof.Coverage.Framer.objects_distinct_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Coverage.Framer.byte_bundle_generated_unsat

end Fang.TptpCandidate.FullFof.Coverage.Framer
