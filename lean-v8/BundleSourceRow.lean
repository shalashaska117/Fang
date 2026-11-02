/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   TSTP source rows for the declarations of a sealed bundle. A row is printed
   with the accepted `SourceRow` pieces, except that a distinct object prints
   as a double-quoted string, and carries `file('<path>',<name>)` with the
   path of the bundle file that holds it. At export time the row is framed
   again by the bundle framer, which must read exactly one formula with the
   declaration's name and body. The accepted lexer has no distinct objects, so
   the reading is the framer's, whose meaning is the bundle semantics. Rows are
   short, so the gated framer frames them; this module imports only the framer
   and the accepted row printer. -/
import BundleFramer
import SourceRow

namespace Fang.QuantifiedEqualityTstp.Expanded.Bundle

open Fang.TptpCandidate.FullFof
open Fang.TptpCandidate.FullFof.Coverage (Bundle File Item Statement statementAt declarationsOf)

/-! Boolean equality on decoded bodies, sound for `=`. The accepted types
    derive no decidable equality, and the deriving handler does not apply to
    the nested source terms. -/

mutual
def termEq : Fang.Source.Term → Fang.Source.Term → Bool
  | .var a, .var b => a == b
  | .app f xs, .app g ys => f == g && termsEq xs ys
  | _, _ => false

def termsEq : List Fang.Source.Term → List Fang.Source.Term → Bool
  | [], [] => true
  | x :: xs, y :: ys => termEq x y && termsEq xs ys
  | _, _ => false
end

mutual
theorem termEq_sound : ∀ {a b : Fang.Source.Term}, termEq a b = true → a = b
  | .var a, .var b, same => by simp only [termEq, beq_iff_eq] at same; rw [same]
  | .app f xs, .app g ys, same => by
    simp only [termEq, Bool.and_eq_true, beq_iff_eq] at same
    rw [same.1, termsEq_sound same.2]
  | .var _, .app _ _, same => by simp [termEq] at same
  | .app _ _, .var _, same => by simp [termEq] at same

theorem termsEq_sound : ∀ {xs ys : List Fang.Source.Term}, termsEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, same => by
    simp only [termsEq, Bool.and_eq_true] at same
    rw [termEq_sound same.1, termsEq_sound same.2]
  | [], _ :: _, same => by simp [termsEq] at same
  | _ :: _, [], same => by simp [termsEq] at same
end

def formulaEq : Formula → Formula → Bool
  | .atom p xs, .atom q ys => p == q && termsEq xs ys
  | .equal l r, .equal l' r' => termEq l l' && termEq r r'
  | .truth, .truth => true
  | .falsity, .falsity => true
  | .neg a, .neg b => formulaEq a b
  | .pair o l r, .pair o' l' r' => o == o' && formulaEq l l' && formulaEq r r'
  | .all x a, .all y b => x == y && formulaEq a b
  | .ex x a, .ex y b => x == y && formulaEq a b
  | _, _ => false

theorem formulaEq_sound : ∀ {a b : Formula}, formulaEq a b = true → a = b
  | .atom p xs, b, same => by
    cases b <;> simp only [formulaEq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at same
    rw [same.1, termsEq_sound same.2]
  | .equal l r, b, same => by
    cases b <;> simp only [formulaEq, Bool.and_eq_true, Bool.false_eq_true] at same
    rw [termEq_sound same.1, termEq_sound same.2]
  | .truth, b, same => by cases b <;> simp_all [formulaEq]
  | .falsity, b, same => by cases b <;> simp_all [formulaEq]
  | .neg a, b, same => by
    cases b <;> simp only [formulaEq, Bool.false_eq_true] at same
    rw [formulaEq_sound same]
  | .pair o l r, b, same => by
    cases b <;> simp only [formulaEq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at same
    rw [same.1.1, formulaEq_sound same.1.2, formulaEq_sound same.2]
  | .all x a, b, same => by
    cases b <;> simp only [formulaEq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at same
    rw [same.1, formulaEq_sound same.2]
  | .ex x a, b, same => by
    cases b <;> simp only [formulaEq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at same
    rw [same.1, formulaEq_sound same.2]

def formulasEq : List Formula → List Formula → Bool
  | [], [] => true
  | a :: left, b :: right => formulaEq a b && formulasEq left right
  | _, _ => false

theorem formulasEq_sound : ∀ {left right : List Formula}, formulasEq left right = true → left = right
  | [], [], _ => rfl
  | a :: left, b :: right, same => by
    simp only [formulasEq, Bool.and_eq_true] at same
    rw [formulaEq_sound same.1, formulasEq_sound same.2]
  | [], _ :: _, same => by simp [formulasEq] at same
  | _ :: _, [], same => by simp [formulasEq] at same

def bodyEq : Body → Body → Bool
  | .cnf left, .cnf right => formulasEq left right
  | .fof a, .fof b => formulaEq a b
  | _, _ => false

theorem bodyEq_sound : ∀ {a b : Body}, bodyEq a b = true → a = b
  | .cnf left, .cnf right, same => by simp only [bodyEq] at same; rw [formulasEq_sound same]
  | .fof a, .fof b, same => by simp only [bodyEq] at same; rw [formulaEq_sound same]
  | .cnf _, .fof _, same => by simp [bodyEq] at same
  | .fof _, .cnf _, same => by simp [bodyEq] at same

/-- A distinct object's content, between double quotes, with `"` and `\` escaped. -/
def objectText (value : String) : String :=
  "\"" ++ String.join ((value.toList.drop 1).map fun c =>
    if c == '"' || c == '\\' then "\\" ++ c.toString else c.toString) ++ "\""

/-- The accepted piece, with the text of a quoted distinct object replaced. -/
def objectPiece (piece : SourceRow.Piece) : SourceRow.Piece :=
  match piece.1 with
  | .legacy (.quoted value) => if Coverage.FramerV2.isObject value then (piece.1, objectText value) else piece
  | _ => piece

def rowText (file : String) (declaration : Declaration) : String :=
  SourceRow.text ((SourceRow.rowPieces "axiom" file declaration).map objectPiece)

def rowBytes (text : String) : List UInt8 := text.toUTF8.data.toList

def maximumRowBytes : Nat := 1048576

/-- One source row, accepted only when the framer reads it back as the declaration. -/
def bundleSourceRow (file : String) (declaration : Declaration) : Except String String :=
  if !SourceRow.bodyOk declaration.body then .error "export-error: CNF body is empty or has an unsupported literal"
  else
    match Coverage.FramerV2.frameFile (rowBytes (rowText file declaration)) maximumRowBytes with
    | .ok [.formula value] =>
      if value.name == declaration.name && bodyEq value.body declaration.body then .ok (rowText file declaration)
      else .error "export-error: source row reads as another declaration"
    | _ => .error "export-error: source row does not frame as one formula"

/-- What a printed row is: its text, and the framer's reading of it. -/
def RowFrames (file : String) (declaration : Declaration) (row : String) : Prop :=
  row = rowText file declaration ∧
    ∃ value, Coverage.FramerV2.frameFile (rowBytes row) maximumRowBytes = .ok [.formula value] ∧
      value.name = declaration.name ∧ value.body = declaration.body

theorem bundleSourceRow_spec {file : String} {declaration : Declaration} {row : String}
    (success : bundleSourceRow file declaration = .ok row) : RowFrames file declaration row := by
  unfold bundleSourceRow at success
  split at success
  · cases success
  · split at success
    · rename_i value framed
      split at success
      · rename_i same
        cases success
        simp only [Bool.and_eq_true, beq_iff_eq] at same
        exact ⟨rfl, value, framed, same.1, bodyEq_sound same.2⟩
      · cases success
    · cases success

/-- The original function table with every distinct object, a NUL-prefixed
    name that cannot print, renamed to `stem` followed by its table index. -/
def renameObjects (stem : String) (functions : List (String × Nat)) : List (String × Nat) :=
  functions.mapIdx fun index entry =>
    if Coverage.FramerV2.isObject entry.1 then (stem ++ toString index, entry.2) else entry

/-- The path a bundle file prints as: its key components joined by `/`. For
    a TPTP-root file this is its path relative to the TPTP root, the way TPTP
    names such files (`Axioms/SET001-0.ax`); it identifies the file uniquely
    in the bundle. -/
def pathOf (file : File) : String := "/".intercalate file.key.path

/-- The declaration at an item, with the path of its file. -/
def sourceItem (bundle : Bundle) (item : Item) : Option (String × Declaration) :=
  match bundle[item.1]? with
  | some file => match file.statements[item.2]? with
    | some (.formula value) => some (pathOf file, value)
    | _ => none
  | none => none

theorem sourceItem_declaration (bundle : Bundle) (item : Item) :
    (sourceItem bundle item).map Prod.snd =
      (match statementAt bundle item with
        | some (.formula value) => some value
        | _ => none) := by
  cases found : bundle[item.1]? with
  | none => simp [sourceItem, statementAt, found]
  | some file =>
    cases entry : file.statements[item.2]? with
    | none => simp [sourceItem, statementAt, found, entry]
    | some statement =>
      cases statement with
      | formula value => simp [sourceItem, statementAt, found, entry]
      | directive parts selection => simp [sourceItem, statementAt, found, entry]

theorem sourceItems_declarations (bundle : Bundle) (items : List Item) :
    (items.filterMap (sourceItem bundle)).map Prod.snd = declarationsOf bundle items := by
  rw [List.map_filterMap, declarationsOf]
  have same : (fun item => (sourceItem bundle item).map Prod.snd) =
      (fun item => match statementAt bundle item with
        | some (.formula value) => some value
        | _ => none) := funext (sourceItem_declaration bundle)
  rw [same]
  -- The two sides use distinct auxiliary match functions with equal bodies.
  rfl

def labelledRow (entry : String × Declaration) : Except String (String × String) := do
  let labelText ← SourceRow.label entry.2.name
  let row ← bundleSourceRow entry.1 entry.2
  pure (labelText, row)

/-- Labels and rows in expansion order. Two files that print the same path
    make export fail, since their rows would name one file. -/
def bundleSourceRows (bundle : Bundle) (items : List Item) : Except String (List (String × String)) :=
  if decide (bundle.map pathOf).Nodup then (items.filterMap (sourceItem bundle)).mapM labelledRow
  else .error "export-error: two bundle files print the same path"

/-- Two lists related element by element, in order. -/
inductive Paired {α β : Type} (P : α → β → Prop) : List α → List β → Prop where
  | nil : Paired P [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} : P a b → Paired P as bs → Paired P (a :: as) (b :: bs)

theorem mapM_paired {α β : Type} {f : α → Except String β} {P : α → β → Prop}
    (step : ∀ a b, f a = .ok b → P a b) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → Paired P xs ys
  | [], ys, success => by
    simp [pure, Except.pure] at success
    subst ys
    exact .nil
  | x :: rest, ys, success => by
    cases head : f x with
    | error reason => simp [List.mapM_cons, head, bind, Except.bind] at success
    | ok value =>
      cases tail : rest.mapM f with
      | error reason => simp [List.mapM_cons, head, tail, bind, Except.bind] at success
      | ok values =>
        simp [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure] at success
        subst ys
        exact .cons (step x value head) (mapM_paired step tail)

def RowsFrame (entries : List (String × Declaration)) (rows : List (String × String)) : Prop :=
  Paired (fun entry row => SourceRow.label entry.2.name = .ok row.1 ∧ RowFrames entry.1 entry.2 row.2)
    entries rows

theorem bundleSourceRows_spec {bundle : Bundle} {items : List Item} {rows : List (String × String)}
    (success : bundleSourceRows bundle items = .ok rows) :
    (bundle.map pathOf).Nodup ∧ RowsFrame (items.filterMap (sourceItem bundle)) rows := by
  unfold bundleSourceRows at success
  split at success
  · rename_i distinct
    refine ⟨of_decide_eq_true distinct, mapM_paired ?_ success⟩
    intro entry row run
    simp only [labelledRow, bind, Except.bind] at run
    cases labelRun : SourceRow.label entry.2.name with
    | error reason => simp [labelRun] at run
    | ok labelText =>
      cases rowRun : bundleSourceRow entry.1 entry.2 with
      | error reason => simp [labelRun, rowRun] at run
      | ok text =>
        simp [labelRun, rowRun, pure, Except.pure] at run
        subst row
        exact ⟨by simp, bundleSourceRow_spec rowRun⟩
  · cases success

/-- The framer reads a row in one way only, so any reading of the printed rows
    has the declarations' bodies, in order. -/
theorem rows_read_bodies {entries : List (String × Declaration)} {rows : List (String × String)}
    (framed : RowsFrame entries rows) :
    ∀ {read : List Declaration},
      Paired (fun row value => Coverage.FramerV2.frameFile (rowBytes row.2) maximumRowBytes = .ok [.formula value])
        rows read →
      read.map Declaration.body = entries.map (Declaration.body ∘ Prod.snd) := by
  induction framed with
  | nil => intro read reading; cases reading; rfl
  | cons head _ ih =>
    intro read reading
    cases reading with
    | cons first rest =>
      obtain ⟨_, _, value, frames, _, sameBody⟩ := head
      rw [frames] at first
      have same := Except.ok.inj first
      simp only [List.cons.injEq, Statement.formula.injEq, and_true] at same
      subst same
      simp [ih rest, sameBody]

#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.termEq_sound
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.termsEq_sound
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.formulaEq_sound
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.formulasEq_sound
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bodyEq_sound
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bundleSourceRow_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.sourceItem_declaration
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.sourceItems_declarations
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.mapM_paired
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.bundleSourceRows_spec
#print axioms Fang.QuantifiedEqualityTstp.Expanded.Bundle.rows_read_bodies

end Fang.QuantifiedEqualityTstp.Expanded.Bundle
