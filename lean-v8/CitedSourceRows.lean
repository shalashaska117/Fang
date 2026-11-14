import RoleFramerDepth
import BundleSourceRow
import GoalRows

namespace Fang.TptpCandidate.CitedDocument.SourceRows
open FullFof Roles.Bundle
open Fang.QuantifiedEqualityTstp.Expanded.Bundle (bodyEq bodyEq_sound objectPiece bundleBodyPieces)

def maximumRowBytes : Nat := 1048576

def frames (maxDepth : Nat) (row : String) :=
  V3.Depth.frameFileHashed 1 maxDepth row.toUTF8.data.toList maximumRowBytes

def SameEntry (expected actual : Roles.Bytes.Entry) : Prop :=
  actual.original.name = expected.original.name ∧ actual.original.body = expected.original.body ∧
    actual.role = expected.role

def Reads (maxDepth : Nat) (row : String) (expected : Roles.Bytes.Entry) : Prop :=
  ∃ actual, frames maxDepth row = .ok [.formula actual] ∧ SameEntry expected actual

def checkedText (maxDepth : Nat) (expected : Roles.Bytes.Entry) (row : String) : Except String String :=
  match frames maxDepth row with
  | .ok [.formula actual] =>
    if actual.original.name == expected.original.name && bodyEq actual.original.body expected.original.body &&
        decide (actual.role = expected.role) then .ok row
    else .error "export-error: source row changes its name, body or role"
  | _ => .error "export-error: source row does not frame as one role declaration"

theorem checkedText_spec {maxDepth expected text row}
    (success : checkedText maxDepth expected text = .ok row) :
    row = text ∧ Reads maxDepth row expected := by
  unfold checkedText at success
  split at success
  · rename_i actual framed
    split at success
    · rename_i same
      cases success
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at same
      exact ⟨rfl, actual, framed, same.1.1, bodyEq_sound same.1.2, same.2⟩
    · cases success
  · cases success

def compactPieces (file : String) (entry : Roles.Bytes.Entry) : List SourceRow.Piece :=
  SourceRow.wordPiece (Grammar.BodyKind entry.original.body) :: SourceRow.punct '(' ::
    SourceRow.namePiece entry.original.name :: SourceRow.punct ',' ::
    SourceRow.wordPiece (GoalRows.roleWord entry.role) :: SourceRow.punct ',' ::
    bundleBodyPieces entry.original.body ++ SourceRow.trailerPieces file entry.original.name

def rowText (maxDepth : Nat) (file : String) (entry : Roles.Bytes.Entry) : String :=
  let original := SourceRow.text ((SourceRow.rowPieces (GoalRows.roleWord entry.role) file entry.original).map objectPiece)
  match frames maxDepth original with
  | .ok [.formula _] => original
  | _ => SourceRow.text ((compactPieces file entry).map objectPiece)

def entryRow (maxDepth : Nat) (file : String) (entry : Roles.Bytes.Entry) : Except String String :=
  if SourceRow.bodyOk entry.original.body then checkedText maxDepth entry (rowText maxDepth file entry)
  else .error "export-error: unsupported source body"

theorem entryRow_spec {maxDepth file entry row}
    (success : entryRow maxDepth file entry = .ok row) :
    row = rowText maxDepth file entry ∧ Reads maxDepth row entry := by
  unfold entryRow at success
  split at success
  · exact checkedText_spec success
  · cases success

def pathOf (file : RoleFile) : String := "/".intercalate file.key.path

def sourceItem (bundle : RoleBundle) (item : Coverage.Item) : Option (String × Roles.Bytes.Entry) :=
  match bundle[item.1]? with
  | some file => match file.statements[item.2]? with
    | some (.formula value) => some (pathOf file, value)
    | _ => none
  | none => none

theorem sourceItem_entry (bundle : RoleBundle) (item : Coverage.Item) :
    (sourceItem bundle item).map Prod.snd =
      (match roleStatementAt bundle item with
        | some (.formula value) => some value
        | _ => none) := by
  cases found : bundle[item.1]? with
  | none => simp [sourceItem, roleStatementAt, found]
  | some file =>
    cases entry : file.statements[item.2]? with
    | none => simp [sourceItem, roleStatementAt, found, entry]
    | some statement =>
      cases statement with
      | formula value => simp [sourceItem, roleStatementAt, found, entry]
      | directive parts selection => simp [sourceItem, roleStatementAt, found, entry]

theorem sourceItems_entries (bundle : RoleBundle) (items : List Coverage.Item) :
    (items.filterMap (sourceItem bundle)).map Prod.snd = entriesOf bundle items := by
  rw [List.map_filterMap, entriesOf]
  have same : (fun item => (sourceItem bundle item).map Prod.snd) =
      (fun item => match roleStatementAt bundle item with
        | some (.formula value) => some value
        | _ => none) := funext (sourceItem_entry bundle)
  rw [same]
  rfl

theorem sourceItem_at {bundle item source} (found : sourceItem bundle item = some source) :
    roleStatementAt bundle item = some (.formula source.2) := by
  have same := sourceItem_entry bundle item
  rw [found] at same
  cases atItem : roleStatementAt bundle item with
  | none => simp [atItem] at same
  | some statement =>
    cases statement with
    | directive parts selection => simp [atItem] at same
    | formula entry =>
      simp only [atItem, Option.map_some, Option.some.injEq] at same
      rw [same]

def labelledRow (maxDepth : Nat) (entry : String × Roles.Bytes.Entry) : Except String (String × String) := do
  let labelText ← SourceRow.label entry.2.original.name
  let row ← entryRow maxDepth entry.1 entry.2
  pure (labelText, row)

def sourceRows (maxDepth : Nat) (bundle : RoleBundle) (items : List Coverage.Item) : Except String (List (String × String)) :=
  if decide (bundle.map pathOf).Nodup then (items.filterMap (sourceItem bundle)).mapM (labelledRow maxDepth)
  else .error "export-error: two bundle files print the same path"

def RowsRead (maxDepth : Nat) (entries : List (String × Roles.Bytes.Entry)) (rows : List (String × String)) : Prop :=
  GoalRows.Paired (fun entry row => SourceRow.label entry.2.original.name = .ok row.1 ∧
    row.2 = rowText maxDepth entry.1 entry.2 ∧ Reads maxDepth row.2 entry.2) entries rows

theorem sourceRows_spec {maxDepth bundle items rows}
    (success : sourceRows maxDepth bundle items = .ok rows) :
    (bundle.map pathOf).Nodup ∧ RowsRead maxDepth (items.filterMap (sourceItem bundle)) rows := by
  unfold sourceRows at success
  split at success
  · rename_i distinct
    refine ⟨of_decide_eq_true distinct, ?_⟩
    apply (GoalRows.mapM_paired success).imp
    intro entry row run
    simp only [labelledRow, Bind.bind, Except.bind] at run
    cases labelRun : SourceRow.label entry.2.original.name with
    | error reason => simp [labelRun] at run
    | ok labelText =>
      cases rowRun : entryRow maxDepth entry.1 entry.2 with
      | error reason => simp [labelRun, rowRun] at run
      | ok text =>
        simp [labelRun, rowRun, Pure.pure, Except.pure] at run
        subst row
        exact ⟨by simp, entryRow_spec rowRun⟩
  · cases success

def negatedEntry (label : String) (formula : Formula) : Roles.Bytes.Entry :=
  { original := ⟨.atom label, .fof (.neg formula), 0, 0, 0, 0⟩, role := .negatedConjecture, roleStart := 0, roleStop := 0 }

def negatedText (label : String) (goal : Name) (formula : Formula) : String :=
  SourceRow.text ((SourceRow.wordPiece "fof" :: SourceRow.punct '(' :: SourceRow.atomPiece label ::
    SourceRow.punct ',' :: SourceRow.wordPiece "negated_conjecture" :: SourceRow.punct ',' ::
    SourceRow.formulaPieces (.neg formula) ++ SourceRow.punct ',' :: GoalRows.inferencePrefix ++
    SourceRow.namePiece goal :: GoalRows.inferenceSuffix).map objectPiece)

def negatedRow (maxDepth : Nat) (label : String) (goal : Name) (formula : Formula) : Except String String := do
  let _ ← SourceRow.label (.atom label)
  let _ ← SourceRow.label goal
  checkedText maxDepth (negatedEntry label formula) (negatedText label goal formula)

theorem negatedRow_spec {maxDepth label goal formula row}
    (success : negatedRow maxDepth label goal formula = .ok row) :
    row = negatedText label goal formula ∧ Reads maxDepth row (negatedEntry label formula) := by
  unfold negatedRow at success
  obtain ⟨_, _, rest⟩ := FangQuantifiedEqualityReplay.bind_success success
  obtain ⟨_, _, checked⟩ := FangQuantifiedEqualityReplay.bind_success rest
  exact checkedText_spec checked

#print axioms checkedText_spec
#print axioms entryRow_spec
#print axioms sourceItem_entry
#print axioms sourceItems_entries
#print axioms sourceItem_at
#print axioms sourceRows_spec
#print axioms negatedRow_spec
end Fang.TptpCandidate.CitedDocument.SourceRows
