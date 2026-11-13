/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Include expansion over a sealed bundle of framed files. Independent Lean
   model of the design; the byte framer and the Rust capture are separate. -/
import ExpandedSource

namespace Fang.TptpCandidate.FullFof.Coverage

inductive Root where
  | base
  | tptp
  deriving DecidableEq, Repr

structure Key where
  root : Root
  path : List String
  deriving DecidableEq, Repr

inductive Selection where
  | absent
  | star
  | names : List Name → Selection
  deriving Repr

/-- A framed statement: a decoded formula record or an include directive. -/
inductive Statement where
  | formula : Declaration → Statement
  | directive : List String → Selection → Statement

structure File where
  key : Key
  statements : List Statement

/-- Files in first-reach order; file 0 is the top-level file. -/
abbrev Bundle := List File

inductive Failure where
  | missing
  | cycle
  | selectionMissing
  | selectionAmbiguous
  | fuel
  deriving DecidableEq, Repr

/-- Source identity: file index and statement index. -/
abbrev Item := Nat × Nat

def statementAt (bundle : Bundle) (item : Item) : Option Statement := do
  let file ← bundle[item.1]?
  file.statements[item.2]?

def nameAt (bundle : Bundle) (item : Item) : Option Name :=
  match statementAt bundle item with
  | some (.formula value) => some value.name
  | _ => none

def lookup (bundle : Bundle) (key : Key) : Option Nat :=
  bundle.findIdx? (fun file => decide (file.key = key))

/-- The including file's directory first, then the TPTP root. -/
def candidates (including : Key) (parts : List String) : List Key :=
  [⟨including.root, including.path.dropLast ++ parts⟩, ⟨.tptp, parts⟩]

def resolve (bundle : Bundle) (including : Key) (parts : List String) : Option Nat :=
  (candidates including parts).findSome? (lookup bundle)

def step (acc : List Item) (item : Item) : List Item :=
  if item ∈ acc then acc else acc ++ [item]

/-- Append items not already present, keeping first occurrences. -/
def addNew (output : List Item) (items : List Item) : List Item :=
  items.foldl step output

def checkNames (bundle : Bundle) (items : List Item) : List Name → Except Failure Unit
  | [] => .ok ()
  | wanted :: rest =>
    match (items.filter (fun item => nameAt bundle item == some wanted)).length with
    | 0 => .error .selectionMissing
    | 1 => checkNames bundle items rest
    | _ + 2 => .error .selectionAmbiguous

def chosen (bundle : Bundle) (wanted : List Name) (item : Item) : Bool :=
  match nameAt bundle item with
  | some label => wanted.contains label
  | none => false

def select (bundle : Bundle) : Selection → List Item → Except Failure (List Item)
  | .names wanted, items => match checkNames bundle items wanted with
    | .error failure => .error failure
    | .ok _ => .ok (items.filter (chosen bundle wanted))
  | _, items => .ok items

def walk (bundle : Bundle) (recurse : List Nat → Nat → Except Failure (List Item))
    (stack : List Nat) (index : Nat) (key : Key) :
    Nat → List Statement → List Item → Except Failure (List Item)
  | _, [], output => .ok output
  | position, .formula _ :: rest, output =>
    walk bundle recurse stack index key (position + 1) rest (addNew output [(index, position)])
  | position, .directive parts selection :: rest, output =>
    match resolve bundle key parts with
    | none => .error .missing
    | some child =>
      if child ∈ stack then .error .cycle
      else match recurse (child :: stack) child with
        | .error failure => .error failure
        | .ok items => match select bundle selection items with
          | .error failure => .error failure
          | .ok kept => walk bundle recurse stack index key (position + 1) rest (addNew output kept)

/-- Complete expansion of one file. Fuel bounds the include depth. -/
def closure (bundle : Bundle) : Nat → List Nat → Nat → Except Failure (List Item)
  | 0, _, _ => .error .fuel
  | fuel + 1, stack, index =>
    match bundle[index]? with
    | none => .error .missing
    | some file => walk bundle (closure bundle fuel) stack index file.key 0 file.statements []

def expand (bundle : Bundle) (fuel : Nat) : Except Failure (List Item) :=
  closure bundle fuel [0] 0

def declarationsOf (bundle : Bundle) (items : List Item) : List Declaration :=
  items.filterMap fun item => match statementAt bundle item with
    | some (.formula value) => some value
    | _ => none

/-- The bundle's meaning: its expanded declarations under the accepted
    source semantics. No filesystem is involved. -/
def BundleSatisfiable (bundle : Bundle) (fuel : Nat) : Prop :=
  ∃ items, expand bundle fuel = .ok items ∧ Satisfiable (source (declarationsOf bundle items))

theorem step_mem {acc : List Item} {first item : Item} :
    item ∈ step acc first ↔ item ∈ acc ∨ item = first := by
  unfold step
  by_cases present : first ∈ acc
  · simp only [present, ↓reduceIte]
    exact ⟨Or.inl, fun h => h.elim id (fun same => same ▸ present)⟩
  · simp [present]

theorem addNew_mem {output items : List Item} {item : Item} :
    item ∈ addNew output items ↔ item ∈ output ∨ item ∈ items := by
  induction items generalizing output with
  | nil => simp [addNew]
  | cons first rest ih =>
    simp only [addNew, List.foldl_cons] at ih ⊢
    rw [ih, step_mem, List.mem_cons]
    exact or_assoc

theorem step_nodup {acc : List Item} (nodup : acc.Nodup) (first : Item) : (step acc first).Nodup := by
  unfold step
  by_cases present : first ∈ acc
  · simpa [present]
  · simp only [present, ↓reduceIte]
    refine List.nodup_append.mpr ⟨nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
    intro a member b single same
    simp only [List.mem_singleton] at single
    subst single
    subst same
    exact present member

theorem addNew_nodup {output : List Item} (nodup : output.Nodup) (items : List Item) :
    (addNew output items).Nodup := by
  induction items generalizing output with
  | nil => simpa [addNew]
  | cons first rest ih =>
    simp only [addNew, List.foldl_cons] at ih ⊢
    exact ih (step_nodup nodup first)

theorem select_subset {bundle : Bundle} {selection : Selection} {items kept : List Item}
    (success : select bundle selection items = .ok kept) {item : Item} (member : item ∈ kept) :
    item ∈ items := by
  cases selection with
  | absent => cases success; exact member
  | star => cases success; exact member
  | names wanted =>
    cases check : checkNames bundle items wanted with
    | error failure => simp [select, check] at success
    | ok done =>
      simp only [select, check, Except.ok.injEq] at success
      subst success
      exact (List.mem_filter.mp member).1

/-- Every selected item has one of the selected names. -/
theorem select_sound {bundle : Bundle} {wanted : List Name} {items kept : List Item}
    (success : select bundle (.names wanted) items = .ok kept) {item : Item}
    (member : item ∈ kept) : ∃ label ∈ wanted, nameAt bundle item = some label := by
  cases check : checkNames bundle items wanted with
  | error failure => simp [select, check] at success
  | ok done =>
    simp only [select, check, Except.ok.injEq] at success
    subst success
    have chose := (List.mem_filter.mp member).2
    simp only [chosen] at chose
    cases at_item : nameAt bundle item with
    | none => simp [at_item] at chose
    | some label =>
      simp only [at_item, List.contains_iff_mem] at chose
      exact ⟨label, chose, rfl⟩

theorem checkNames_exact {bundle : Bundle} {items : List Item} {wanted : List Name}
    (success : checkNames bundle items wanted = .ok ()) :
    ∀ label ∈ wanted, (items.filter (fun item => nameAt bundle item == some label)).length = 1 := by
  induction wanted with
  | nil => simp
  | cons first rest ih =>
    intro label member
    simp only [checkNames] at success
    split at success
    · cases success
    · rcases List.mem_cons.mp member with rfl | member
      · assumption
      · exact ih success label member
    · cases success

/-- Every selected name matches exactly one formula of the expansion. -/
theorem select_exact {bundle : Bundle} {wanted : List Name} {items kept : List Item}
    (success : select bundle (.names wanted) items = .ok kept) :
    ∀ label ∈ wanted, (items.filter (fun item => nameAt bundle item == some label)).length = 1 := by
  cases check : checkNames bundle items wanted with
  | error failure => simp [select, check] at success
  | ok done => exact checkNames_exact check

def IsFormula (bundle : Bundle) (item : Item) : Prop :=
  ∃ value, statementAt bundle item = some (.formula value)

theorem walk_formulas {bundle : Bundle} {recurse : List Nat → Nat → Except Failure (List Item)}
    (recursive : ∀ stack child items, recurse stack child = .ok items → ∀ item ∈ items, IsFormula bundle item)
    {stack : List Nat} {index : Nat} {file : File} (at_index : bundle[index]? = some file)
    {position : Nat} {list : List Statement} (suffix : file.statements.drop position = list)
    {output result : List Item} (prior : ∀ item ∈ output, IsFormula bundle item)
    (success : walk bundle recurse stack index file.key position list output = .ok result) :
    ∀ item ∈ result, IsFormula bundle item := by
  induction list generalizing position output with
  | nil =>
    simp only [walk] at success
    cases success
    exact prior
  | cons first rest ih =>
    have here : file.statements[position]? = some first := by
      rw [← List.head?_drop, suffix]; rfl
    have next : file.statements.drop (position + 1) = rest := by
      rw [← List.drop_drop, suffix]; rfl
    cases first with
    | formula value =>
      simp only [walk] at success
      refine ih next ?_ success
      intro item member
      rcases addNew_mem.mp member with old | new
      · exact prior item old
      · simp only [List.mem_singleton] at new
        subst new
        exact ⟨value, by simp [statementAt, at_index, here]⟩
    | directive parts selection =>
      simp only [walk] at success
      split at success
      · cases success
      · rename_i child _
        split at success
        · cases success
        · split at success
          · cases success
          · rename_i items called
            split at success
            · cases success
            · rename_i kept selected
              refine ih next ?_ success
              intro item member
              rcases addNew_mem.mp member with old | new
              · exact prior item old
              · exact recursive _ _ _ called item (select_subset selected new)

/-- Every expanded source identity names a formula statement in the bundle. -/
theorem closure_formulas {bundle : Bundle} :
    ∀ fuel stack index result, closure bundle fuel stack index = .ok result →
      ∀ item ∈ result, IsFormula bundle item := by
  intro fuel
  induction fuel with
  | zero => intro stack index result success; simp [closure] at success
  | succ fuel ih =>
    intro stack index result success
    simp only [closure] at success
    split at success
    · cases success
    · rename_i file at_index
      exact walk_formulas (fun s c i h => ih s c i h) at_index (by simp) (by simp) success

theorem walk_nodup {bundle : Bundle} {recurse : List Nat → Nat → Except Failure (List Item)}
    {stack : List Nat} {index : Nat} {key : Key} {position : Nat} {list : List Statement}
    {output result : List Item} (nodup : output.Nodup)
    (success : walk bundle recurse stack index key position list output = .ok result) :
    result.Nodup := by
  induction list generalizing position output with
  | nil => simp only [walk] at success; cases success; exact nodup
  | cons first rest ih =>
    cases first with
    | formula value =>
      simp only [walk] at success
      exact ih (addNew_nodup nodup _) success
    | directive parts selection =>
      simp only [walk] at success
      split at success
      · cases success
      · split at success
        · cases success
        · split at success
          · cases success
          · split at success
            · cases success
            · exact ih (addNew_nodup nodup _) success

/-- No source identity appears twice in an expansion. -/
theorem closure_nodup {bundle : Bundle} {fuel : Nat} {stack : List Nat} {index : Nat}
    {result : List Item} (success : closure bundle fuel stack index = .ok result) : result.Nodup := by
  cases fuel with
  | zero => simp [closure] at success
  | succ fuel =>
    simp only [closure] at success
    split at success
    · cases success
    · exact walk_nodup List.nodup_nil success

/-- Consecutive statement positions of one file. -/
def positions (index : Nat) : Nat → Nat → List Item
  | _, 0 => []
  | position, count + 1 => (index, position) :: positions index (position + 1) count

theorem mem_positions {index position count : Nat} {item : Item} :
    item ∈ positions index position count ↔ item.1 = index ∧ position ≤ item.2 ∧ item.2 < position + count := by
  induction count generalizing position with
  | zero => simp [positions]
  | succ count ih =>
    simp only [positions, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨a, b, c⟩) <;> simp_all <;> omega
    · rintro ⟨a, b, c⟩
      by_cases same : item.2 = position
      · exact .inl (Prod.ext a same)
      · exact .inr ⟨a, by omega, by omega⟩

/-- A file without includes contributes its formulas in order. -/
theorem walk_plain {bundle : Bundle} {recurse : List Nat → Nat → Except Failure (List Item)}
    {stack : List Nat} {index : Nat} {key : Key} (values : List Declaration) :
    ∀ position output, (∀ item ∈ output, item.1 = index → item.2 < position) →
      walk bundle recurse stack index key position (values.map .formula) output =
        .ok (output ++ positions index position values.length) := by
  induction values with
  | nil => intro position output _; simp [walk, positions]
  | cons first rest ih =>
    intro position output earlier
    have absent : (index, position) ∉ output := fun member => by
      have := earlier _ member rfl
      omega
    simp only [List.map_cons, walk, addNew, step, List.foldl_cons, List.foldl_nil, absent, ↓reduceIte]
    rw [ih (position + 1)]
    · simp [positions]
    · intro item member same
      rcases List.mem_append.mp member with old | new
      · have := earlier item old same
        omega
      · simp only [List.mem_singleton] at new
        subst new
        simp

theorem declarationsOf_positions (key : Key) (values : List Declaration) :
    ∀ count position, declarationsOf [⟨key, values.map .formula⟩] (positions 0 position count) =
      (values.drop position).take count := by
  intro count
  induction count with
  | zero => intro position; simp [positions, declarationsOf]
  | succ count ih =>
    intro position
    have tail := ih (position + 1)
    simp only [declarationsOf] at tail ⊢
    simp only [positions, List.filterMap_cons, tail]
    by_cases inside : position < values.length
    · have at_position : statementAt [⟨key, values.map .formula⟩] (0, position) =
          some (.formula values[position]) := by
        simp [statementAt, inside]
      simp only [at_position]
      rw [List.drop_eq_getElem_cons inside, List.take_succ_cons]
    · have at_position : statementAt [⟨key, values.map .formula⟩] (0, position) = none := by
        simp [statementAt]
        omega
      simp only [at_position]
      simp [List.drop_eq_nil_of_le (Nat.le_of_not_lt inside)]
      omega

theorem expand_single (key : Key) (values : List Declaration) (fuel : Nat) :
    expand [⟨key, values.map .formula⟩] (fuel + 1) = .ok (positions 0 0 values.length) := by
  simp only [expand, closure, List.getElem?_cons_zero]
  rw [walk_plain values 0 [] (by simp)]
  simp

theorem declarationsOf_single (key : Key) (values : List Declaration) :
    declarationsOf [⟨key, values.map .formula⟩] (positions 0 0 values.length) = values := by
  rw [declarationsOf_positions]
  simp

/-- One file without includes means exactly what the accepted decoder says. -/
theorem bundle_single_satisfiable (key : Key) (values : List Declaration) (fuel : Nat) :
    BundleSatisfiable [⟨key, values.map .formula⟩] (fuel + 1) ↔ Satisfiable (source values) := by
  constructor
  · rintro ⟨items, expanded, holds⟩
    rw [expand_single] at expanded
    cases expanded
    rwa [declarationsOf_single] at holds
  · intro holds
    exact ⟨_, expand_single key values fuel, by rwa [declarationsOf_single]⟩

theorem bundle_single_bytes {bytes : List UInt8} {maximum : Nat} {values : List Declaration}
    (decoded : CnfBoolean.decodeBytes bytes maximum = .ok values) (key : Key) (fuel : Nat) :
    BundleSatisfiable [⟨key, values.map .formula⟩] (fuel + 1) ↔
      CnfBoolean.BytesSatisfiable bytes maximum :=
  (bundle_single_satisfiable key values fuel).trans (CnfBoolean.decode_bytes_satisfiable decoded).symm

/-- Bundle refutation through the accepted numeric input semantics. -/
theorem bundle_input_unsat {bundle : Bundle} {fuel : Nat} {items : List Item}
    {input : Integration.NumericInput} (expanded : expand bundle fuel = .ok items)
    (encoded : Integration.readInput (declarationsOf bundle items) = some input)
    (closed : Grammar.Closed (declarationsOf bundle items))
    (refuted : ¬ input.Satisfiable) : ¬ BundleSatisfiable bundle fuel := by
  rintro ⟨found, again, holds⟩
  rw [expanded] at again
  cases again
  exact refuted ((Integration.readInput_satisfiable encoded closed).mp holds)

#print axioms Fang.TptpCandidate.FullFof.Coverage.addNew_mem
#print axioms Fang.TptpCandidate.FullFof.Coverage.addNew_nodup
#print axioms Fang.TptpCandidate.FullFof.Coverage.select_subset
#print axioms Fang.TptpCandidate.FullFof.Coverage.select_sound
#print axioms Fang.TptpCandidate.FullFof.Coverage.checkNames_exact
#print axioms Fang.TptpCandidate.FullFof.Coverage.select_exact
#print axioms Fang.TptpCandidate.FullFof.Coverage.walk_formulas
#print axioms Fang.TptpCandidate.FullFof.Coverage.closure_formulas
#print axioms Fang.TptpCandidate.FullFof.Coverage.walk_nodup
#print axioms Fang.TptpCandidate.FullFof.Coverage.closure_nodup
#print axioms Fang.TptpCandidate.FullFof.Coverage.mem_positions
#print axioms Fang.TptpCandidate.FullFof.Coverage.walk_plain
#print axioms Fang.TptpCandidate.FullFof.Coverage.declarationsOf_positions
#print axioms Fang.TptpCandidate.FullFof.Coverage.expand_single
#print axioms Fang.TptpCandidate.FullFof.Coverage.declarationsOf_single
#print axioms Fang.TptpCandidate.FullFof.Coverage.bundle_single_satisfiable
#print axioms Fang.TptpCandidate.FullFof.Coverage.bundle_single_bytes
#print axioms Fang.TptpCandidate.FullFof.Coverage.bundle_input_unsat

end Fang.TptpCandidate.FullFof.Coverage
