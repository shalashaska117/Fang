/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   Signed numeric tasks: complete original tables first, then one task per original goal. -/
import RoleModels
import ExpandedSource

namespace Fang.TptpCandidate.Roles.Numeric
open FullFof

/-! Closed numeric formulas do not depend on the valuation. -/

theorem term_eval_agree {D : Type} (model : Interpretation D) {bound : List Nat}
    {left right : Nat → D} (same : ∀ id ∈ bound, left id = right id) (term : Term)
    (within : QuantifiedFOF.TermWithin bound term) : term.eval model left = term.eval model right := by
  cases term with
  | var id =>
    simp only [QuantifiedFOF.TermWithin] at within
    simp only [Term.eval]
    exact same id within
  | app symbol args =>
    simp only [QuantifiedFOF.TermWithin] at within
    simp only [Term.eval]
    congr 1
    apply List.map_congr_left
    intro child member
    exact term_eval_agree model same child (within child member)
termination_by sizeOf term

theorem update_agree {D : Type} {bound : List Nat} {left right : Nat → D}
    (same : ∀ id ∈ bound, left id = right id) (binder : Nat) (value : D) :
    ∀ id ∈ binder :: bound,
      QuantifiedFOF.update left binder value id = QuantifiedFOF.update right binder value id := by
  intro id member
  by_cases equal : id = binder
  · simp [QuantifiedFOF.update, equal]
  · simp only [QuantifiedFOF.update, equal, ite_false]
    exact same id ((List.mem_cons.mp member).resolve_left equal)

theorem holds_agree {D : Type} (model : Interpretation D) (formula : QuantifiedFOF.Formula) :
    ∀ {bound : List Nat} {left right : Nat → D}, (∀ id ∈ bound, left id = right id) →
      formula.Within bound → (formula.Holds model left ↔ formula.Holds model right) := by
  induction formula with
  | atom atom =>
    intro bound left right same within
    simp only [QuantifiedFOF.Formula.Within] at within
    have args : atom.args.map (Term.eval model left) = atom.args.map (Term.eval model right) :=
      List.map_congr_left (fun term member => term_eval_agree model same term (within term member))
    simp only [QuantifiedFOF.Formula.Holds, Atom.Holds, args]
  | truth => intro _ _ _ _ _; exact Iff.rfl
  | falsity => intro _ _ _ _ _; exact Iff.rfl
  | neg body ih =>
    intro bound left right same within
    exact not_congr (ih same within)
  | conj first second ihFirst ihSecond =>
    intro bound left right same within
    exact and_congr (ihFirst same within.1) (ihSecond same within.2)
  | disj first second ihFirst ihSecond =>
    intro bound left right same within
    exact or_congr (ihFirst same within.1) (ihSecond same within.2)
  | implies first second ihFirst ihSecond =>
    intro bound left right same within
    exact imp_congr (ihFirst same within.1) (ihSecond same within.2)
  | all binder body ih =>
    intro bound left right same within
    exact forall_congr' fun value => ih (update_agree same binder value) within
  | ex binder body ih =>
    intro bound left right same within
    exact exists_congr fun value => ih (update_agree same binder value) within

theorem closed_holds_independent {D : Type} (model : Interpretation D)
    {formula : QuantifiedFOF.Formula} (closed : formula.Within []) (left right : Nat → D) :
    formula.Holds model left ↔ formula.Holds model right :=
  holds_agree model formula (fun id member => by cases member) closed

/-- Failure of a closed sentence is exactly the negative sign holding everywhere. A nonempty domain supplies a valuation for the reverse direction. -/
theorem closed_failure_iff {D : Type} [inhabited : Nonempty D] (model : Interpretation D)
    {formula : QuantifiedFOF.Formula} (closed : formula.Within []) :
    (¬ ∀ valuation, formula.Holds model valuation) ↔
      ∀ valuation, GroundFOF.signed false (formula.Holds model valuation) := by
  simp only [GroundFOF.signed, Bool.false_eq_true, ite_false]
  constructor
  · intro fails valuation holds
    exact fails (fun other => (closed_holds_independent model closed valuation other).mp holds)
  · intro negative holds
    let point : D := Classical.choice inhabited
    exact negative (fun _ => point) (holds (fun _ => point))

/-- The same statement for an original named sentence: its failure is the universal truth of the original formula under one negation. -/
theorem named_failure_iff {D : Type} [Nonempty D] (model : Source.Interpretation D)
    {formula : FullFof.Formula} (closed : formula.Within []) :
    ¬ Bytes.sentence model formula ↔ Bytes.sentence model (FullFof.Formula.neg formula) := by
  let functions := FullFof.functionTable [formula]
  let predicates := FullFof.predicateTable [formula]
  have covered : formula.Covered functions predicates formula.variables :=
    collected_covered (List.mem_singleton_self formula)
  have agree := model_toNumeric model functions predicates
  let encoded := formula.encode functions predicates formula.variables
  have encodedClosed : encoded.Within [] := by
    simpa using Integration.encoded_formula_within formula functions predicates formula.variables [] closed
  have pointwise (valuation : Nat → D) :
      encoded.Holds (FullFof.toNumeric model functions predicates) valuation ↔
        formula.Holds model (fun name => valuation (formula.variables.id name)) :=
    encode_holds covered agree _ valuation (fun _ _ => rfl)
  have back (valuation : String → D) :
      encoded.Holds (FullFof.toNumeric model functions predicates)
          (fun id => valuation (formula.variables.name id)) ↔ formula.Holds model valuation :=
    encode_holds covered agree valuation _ (fun _ represented => congrArg valuation represented.symm)
  have sentenceIff : Bytes.sentence model formula ↔
      ∀ valuation, encoded.Holds (FullFof.toNumeric model functions predicates) valuation :=
    ⟨fun holds valuation => (pointwise valuation).mpr (holds _),
     fun holds valuation => (back valuation).mp (holds _)⟩
  have negatedIff : Bytes.sentence model (FullFof.Formula.neg formula) ↔
      ∀ valuation, GroundFOF.signed false
        (encoded.Holds (FullFof.toNumeric model functions predicates) valuation) := by
    simp only [GroundFOF.signed, Bool.false_eq_true, ite_false]
    exact ⟨fun holds valuation => fun inner => holds _ ((pointwise valuation).mp inner),
     fun holds valuation => fun inner => holds _ ((back valuation).mpr inner)⟩
  rw [sentenceIff, negatedIff]
  exact closed_failure_iff _ encodedClosed

/-! Original rows under the complete original tables. -/

/-- One original declaration with its role and its reviewed numeric block. -/
structure RoleRow where
  role : Role
  row : Integration.NumericRow

def RoleRow.declaration (value : RoleRow) : Roles.Declaration Name FullFof.Formula :=
  ⟨value.row.original.name, value.role, value.row.original.body.formula⟩

/-- The same `readBody` call as the reviewed `readRows`, with the role kept beside it. -/
def readRoleRows (functions predicates : Arity.Table) :
    List Bytes.Entry → Option (List RoleRow)
  | [] => some []
  | value :: rest => do
    let block ← Integration.readBody functions predicates value.original.body
    let tail ← readRoleRows functions predicates rest
    pure (⟨value.role, ⟨value.original, block⟩⟩ :: tail)

structure SignedInput where
  functions : Arity.Table
  predicates : Arity.Table
  rows : List RoleRow

/-- Both tables come from every original declaration, conjectures included, before any goal is selected. No spelling-only symbol guard is applied. -/
def readSigned (values : List Bytes.Entry) : Option SignedInput := do
  let originals := values.map Bytes.Entry.original
  let functions := FullFof.functionTable (FullFof.source originals)
  let predicates := FullFof.predicateTable (FullFof.source originals)
  let rows ← readRoleRows functions predicates values
  pure ⟨functions, predicates, rows⟩

theorem readRoleRows_exact {functions predicates values rows}
    (success : readRoleRows functions predicates values = some rows) :
    Integration.readRows functions predicates (values.map Bytes.Entry.original) =
        some (rows.map RoleRow.row) ∧
      rows.map RoleRow.declaration = Bytes.source values := by
  induction values generalizing rows with
  | nil =>
    cases Option.some.inj success
    exact ⟨rfl, rfl⟩
  | cons first rest ih =>
    cases bodyAt : Integration.readBody functions predicates first.original.body with
    | none => simp [readRoleRows, bodyAt] at success
    | some block =>
      cases tailAt : readRoleRows functions predicates rest with
      | none => simp [readRoleRows, bodyAt, tailAt] at success
      | some tail =>
        have same : (⟨first.role, ⟨first.original, block⟩⟩ :: tail : List RoleRow) = rows :=
          Option.some.inj (by simpa [readRoleRows, bodyAt, tailAt] using success)
        subst rows
        obtain ⟨rowsRun, sources⟩ := ih tailAt
        constructor
        · simp [Integration.readRows, bodyAt, rowsRun]
        · simp only [List.map_cons, RoleRow.declaration]
          rw [sources]
          rfl

theorem readRoleRows_member {functions predicates values rows}
    (success : readRoleRows functions predicates values = some rows) {row} (member : row ∈ rows) :
    ∃ value ∈ values, row.role = value.role ∧ row.row.original = value.original ∧
      Integration.readBody functions predicates value.original.body = some row.row.declarations := by
  induction values generalizing rows with
  | nil =>
    cases Option.some.inj success
    simp at member
  | cons first rest ih =>
    cases bodyAt : Integration.readBody functions predicates first.original.body with
    | none => simp [readRoleRows, bodyAt] at success
    | some block =>
      cases tailAt : readRoleRows functions predicates rest with
      | none => simp [readRoleRows, bodyAt, tailAt] at success
      | some tail =>
        have same : (⟨first.role, ⟨first.original, block⟩⟩ :: tail : List RoleRow) = rows :=
          Option.some.inj (by simpa [readRoleRows, bodyAt, tailAt] using success)
        subst rows
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨first, List.mem_cons_self, rfl, rfl, bodyAt⟩
        · obtain ⟨value, present, role, original, body⟩ := ih tailAt member
          exact ⟨value, List.mem_cons_of_mem _ present, role, original, body⟩

/-- The rows are exactly the reviewed `readInput` result for the same originals. -/
theorem readSigned_exact {values input} (success : readSigned values = some input) :
    Integration.readInput (values.map Bytes.Entry.original) =
        some ⟨input.functions, input.predicates, input.rows.map RoleRow.row⟩ ∧
      input.functions = FullFof.functionTable (FullFof.source (values.map Bytes.Entry.original)) ∧
      input.predicates = FullFof.predicateTable (FullFof.source (values.map Bytes.Entry.original)) ∧
      input.rows.map RoleRow.declaration = Bytes.source values := by
  cases rowsAt : readRoleRows (FullFof.functionTable (FullFof.source (values.map Bytes.Entry.original)))
      (FullFof.predicateTable (FullFof.source (values.map Bytes.Entry.original))) values with
  | none => simp [readSigned, rowsAt] at success
  | some rows =>
    have same : (⟨FullFof.functionTable (FullFof.source (values.map Bytes.Entry.original)),
        FullFof.predicateTable (FullFof.source (values.map Bytes.Entry.original)), rows⟩ : SignedInput) = input :=
      Option.some.inj (by simpa [readSigned, rowsAt] using success)
    subst input
    obtain ⟨rowsRun, sources⟩ := readRoleRows_exact rowsAt
    exact ⟨by simp [Integration.readInput, rowsRun], rfl, rfl, sources⟩

/-- Every row has its reviewed block, complete-table coverage and closure. -/
theorem readSigned_row {values input} (success : readSigned values = some input)
    (closed : Bytes.Closed values) {row} (member : row ∈ input.rows) :
    Integration.readBody input.functions input.predicates row.row.original.body = some row.row.declarations ∧
      row.row.original.body.formula.Covered input.functions input.predicates
        row.row.original.body.formula.variables ∧
      Integration.BodyClosed row.row.original.body := by
  cases rowsAt : readRoleRows (FullFof.functionTable (FullFof.source (values.map Bytes.Entry.original)))
      (FullFof.predicateTable (FullFof.source (values.map Bytes.Entry.original))) values with
  | none => simp [readSigned, rowsAt] at success
  | some rows =>
    have same : (⟨FullFof.functionTable (FullFof.source (values.map Bytes.Entry.original)),
        FullFof.predicateTable (FullFof.source (values.map Bytes.Entry.original)), rows⟩ : SignedInput) = input :=
      Option.some.inj (by simpa [readSigned, rowsAt] using success)
    subst input
    obtain ⟨value, present, _, original, body⟩ := readRoleRows_member rowsAt member
    refine ⟨by rw [original]; exact body, ?_, ?_⟩
    · rw [original]
      exact collected_covered (List.mem_map.mpr
        ⟨value.original, List.mem_map.mpr ⟨value, present, rfl⟩, rfl⟩)
    · rw [original]
      have shape := closed value present
      cases bodyShape : value.original.body with
      | cnf _ => trivial
      | fof formula => simpa [Integration.BodyClosed, bodyShape] using shape

/-- Reuse of the reviewed body model lemma for any original row. -/
theorem row_models {values input} (success : readSigned values = some input)
    (closed : Bytes.Closed values) {row} (member : row ∈ input.rows)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement input.functions input.predicates named numeric) :
    NamedQuantified.NumericModels numeric row.row.declarations ↔
      Bytes.sentence named row.row.original.body.formula := by
  obtain ⟨body, covered, bodyClosed⟩ := readSigned_row success closed member
  exact Integration.readBody_models body covered bodyClosed models

/-- An FOF block from `readBody` is the original formula encoded with the original formula's own variable map. CNF bodies never produce it. -/
theorem readBody_fof {functions predicates body formula}
    (success : Integration.readBody functions predicates body = some [.fof formula]) :
    ∃ original, body = .fof original ∧
      formula = original.encode functions predicates original.variables := by
  cases body with
  | fof original =>
    have same : ([.fof (original.encode functions predicates original.variables)] :
        List NamedQuantified.NumericDeclaration) = [.fof formula] := Option.some.inj success
    simp only [List.cons.injEq, NamedQuantified.NumericDeclaration.fof.injEq, and_true] at same
    exact ⟨original, rfl, same.symm⟩
  | cnf literals =>
    cases result : Integration.readClause functions predicates (Body.cnf literals).formula.variables literals with
    | none => simp [Integration.readBody, result] at success
    | some output =>
      cases output <;> simp [Integration.readBody, result, Integration.cnfBlock] at success

/-! Signed items, tasks and their semantics. -/

/-- CNF items are always positive. Only an FOF item carries a sign. -/
inductive SignedNumeric where
  | cnf : Fang.Clause → SignedNumeric
  | fof : Bool → QuantifiedFOF.Formula → SignedNumeric
  deriving Repr

def SignedNumeric.Holds {D : Type} (model : Interpretation D) : SignedNumeric → Prop
  | .cnf clause => clause.Valid model
  | .fof positive formula =>
    formula.Within [] ∧ ∀ valuation, GroundFOF.signed positive (formula.Holds model valuation)

def TaskModels {D : Type} (model : Interpretation D) (task : List SignedNumeric) : Prop :=
  ∀ item ∈ task, item.Holds model

/-- The final reserved predicate is mathematical equality, as in `NumericInput.Satisfiable`. -/
def TaskSatisfiable (input : SignedInput) (task : List SignedNumeric) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (model : Interpretation D),
    TaskModels (FullFof.reserve input.predicates.length model) task

def positive : NamedQuantified.NumericDeclaration → SignedNumeric
  | .cnf clause => .cnf clause
  | .fof formula => .fof true formula

def isPremise (role : Role) : Bool := decide (classify role = .ok .premise)

def isPositiveInput (role : Role) : Bool :=
  decide (classify role = .ok .premise ∨ classify role = .ok .alreadyNegated)

/-- Rows whose role passes `select` contribute their unchanged block, in source order. -/
def selectBlock (select : Role → Bool) (rows : List RoleRow) : List SignedNumeric :=
  rows.flatMap (fun row => if select row.role then row.row.declarations.map positive else [])

/-- The selected goal keeps its own encoded formula; only the sign changes. -/
def negativeGoal (row : RoleRow) : Option SignedNumeric :=
  match row.row.declarations with
  | [.fof formula] => some (.fof false formula)
  | _ => none

/-- One original goal: all premises in source order and that goal with the negative sign at its source position. Other goals are excluded. -/
def goalTask (before : List RoleRow) (goal : RoleRow) (after : List RoleRow) :
    Option (List SignedNumeric) :=
  if goal.role = .conjecture then
    (negativeGoal goal).map (fun negated =>
      selectBlock isPremise before ++ negated :: selectBlock isPremise after)
  else none

/-- Without an original goal: every accepted positive input, already negated conjectures included, and no negative item. -/
def inputsTask (input : SignedInput) : List SignedNumeric :=
  selectBlock isPositiveInput input.rows

/-- Every way to select one row with its exact source context. -/
def splits {α : Type} : List α → List (List α × α × List α)
  | [] => []
  | head :: tail => ([], head, tail) :: (splits tail).map (fun split => (head :: split.1, split.2))

theorem mem_splits {α : Type} : ∀ {values : List α} {before : List α} {item : α} {after : List α},
    (before, item, after) ∈ splits values ↔ values = before ++ item :: after
  | [], before, item, after => by cases before <;> simp [splits]
  | head :: tail, [], item, after => by
    simp only [splits, List.mem_cons, List.mem_map, List.nil_append, List.cons.injEq]
    constructor
    · rintro (same | ⟨⟨first, middle, last⟩, -, image⟩)
      · cases same
        exact ⟨rfl, rfl⟩
      · simp at image
    · rintro ⟨rfl, rfl⟩
      exact Or.inl rfl
  | head :: tail, first :: rest, item, after => by
    simp only [splits, List.mem_cons, List.mem_map, List.cons_append, List.cons.injEq]
    constructor
    · rintro (same | ⟨⟨start, middle, last⟩, member, image⟩)
      · simp at same
      · simp only [Prod.mk.injEq, List.cons.injEq] at image
        obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := image
        exact ⟨rfl, mem_splits.mp member⟩
    · rintro ⟨rfl, rfl⟩
      exact Or.inr ⟨(rest, item, after), mem_splits.mpr rfl, rfl⟩

/-- Ordered obligations, one per original conjecture. A CNF conjecture, which the decoder rejects, would make the whole list `none`. -/
def goalTasks (input : SignedInput) : Option (List (List SignedNumeric)) :=
  ((splits input.rows).filter (fun split => decide (split.2.1.role = .conjecture))).mapM
    (fun split => goalTask split.1 split.2.1 split.2.2)

theorem positive_holds {D : Type} (model : Interpretation D)
    (declaration : NamedQuantified.NumericDeclaration) :
    (positive declaration).Holds model ↔ declaration.Models model := by
  cases declaration <;>
    simp [positive, SignedNumeric.Holds, NamedQuantified.NumericDeclaration.Models, GroundFOF.signed]

theorem taskModels_append {D : Type} (model : Interpretation D) (left right : List SignedNumeric) :
    TaskModels model (left ++ right) ↔ TaskModels model left ∧ TaskModels model right := by
  simp only [TaskModels, List.forall_mem_append]

theorem taskModels_cons {D : Type} (model : Interpretation D) (item : SignedNumeric)
    (rest : List SignedNumeric) :
    TaskModels model (item :: rest) ↔ item.Holds model ∧ TaskModels model rest := by
  simp only [TaskModels, List.forall_mem_cons]

theorem selectBlock_models {values input} (success : readSigned values = some input)
    (closed : Bytes.Closed values) (select : Role → Bool)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement input.functions input.predicates named numeric) :
    ∀ {rows : List RoleRow}, (∀ row ∈ rows, row ∈ input.rows) →
      (TaskModels numeric (selectBlock select rows) ↔
        ∀ row ∈ rows, select row.role = true → Bytes.sentence named row.row.original.body.formula)
  | [], _ => by simp [selectBlock, TaskModels]
  | row :: rest, inside => by
    have tail := selectBlock_models success closed select models
      (rows := rest) (fun other member => inside other (List.mem_cons_of_mem _ member))
    have head := row_models success closed (inside row List.mem_cons_self) models
    rw [show selectBlock select (row :: rest) =
        (if select row.role then row.row.declarations.map positive else []) ++ selectBlock select rest
      from List.flatMap_cons, taskModels_append, tail, List.forall_mem_cons]
    apply and_congr_left'
    cases selected : select row.role with
    | false => simp [TaskModels]
    | true =>
      rw [← head]
      simp [TaskModels, positive_holds, NamedQuantified.NumericModels]

theorem allHold_select {D : Type} (named : Source.Interpretation D) (rows : List RoleRow)
    (select : Role → Bool) :
    Roles.AllHold (Bytes.sentence (D := D))
        ((rows.map RoleRow.declaration).filter (fun declaration => select declaration.role)) named ↔
      ∀ row ∈ rows, select row.role = true → Bytes.sentence named row.row.original.body.formula := by
  simp [Roles.AllHold, List.mem_filter, RoleRow.declaration]

theorem conjecture_not_premise {role : Role} (goal : role = .conjecture) : isPremise role = false := by
  subst role
  rfl

theorem goalTask_shape {before goal after items}
    (task : goalTask before goal after = some items) :
    goal.role = .conjecture ∧ ∃ formula, goal.row.declarations = [.fof formula] ∧
      items = selectBlock isPremise before ++ .fof false formula :: selectBlock isPremise after := by
  unfold goalTask at task
  split at task
  · rename_i role
    refine ⟨role, ?_⟩
    unfold negativeGoal at task
    split at task
    · rename_i formula shape
      exact ⟨formula, shape, (Option.some.inj task).symm⟩
    · simp at task
  · cases task

def isNegative : SignedNumeric → Bool
  | .fof false _ => true
  | _ => false

theorem selectBlock_member {select : Role → Bool} {rows : List RoleRow} {item : SignedNumeric}
    (member : item ∈ selectBlock select rows) :
    ∃ row ∈ rows, select row.role = true ∧
      ∃ declaration ∈ row.row.declarations, item = positive declaration := by
  simp only [selectBlock, List.mem_flatMap] at member
  obtain ⟨row, rowMember, inside⟩ := member
  cases selected : select row.role with
  | false => simp [selected] at inside
  | true =>
    have mapped : item ∈ row.row.declarations.map positive := by simpa [selected] using inside
    obtain ⟨declaration, present, same⟩ := List.mem_map.mp mapped
    exact ⟨row, rowMember, selected, declaration, present, same.symm⟩

theorem selectBlock_contains {select : Role → Bool} {rows : List RoleRow} {row : RoleRow}
    (member : row ∈ rows) (selected : select row.role = true)
    {declaration} (present : declaration ∈ row.row.declarations) :
    positive declaration ∈ selectBlock select rows := by
  simp only [selectBlock, List.mem_flatMap]
  refine ⟨row, member, ?_⟩
  split
  · exact List.mem_map_of_mem present
  · rename_i notSelected
    exact absurd selected notSelected

theorem positive_not_negative (declaration : NamedQuantified.NumericDeclaration) :
    isNegative (positive declaration) = false := by
  cases declaration <;> rfl

theorem selectBlock_no_negative (select : Role → Bool) (rows : List RoleRow) :
    (selectBlock select rows).filter isNegative = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro item member
  obtain ⟨_, _, _, declaration, _, rfl⟩ := selectBlock_member member
  simp [positive_not_negative]

/-- A goal task has exactly one negative item: the goal row's own formula. -/
theorem goalTask_negative_items {before goal after items}
    (task : goalTask before goal after = some items) :
    ∃ formula, goal.row.declarations = [.fof formula] ∧
      items.filter isNegative = [.fof false formula] := by
  obtain ⟨_, formula, shape, rfl⟩ := goalTask_shape task
  refine ⟨formula, shape, ?_⟩
  rw [List.filter_append, List.filter_cons, selectBlock_no_negative, selectBlock_no_negative]
  simp [isNegative]

/-- Every premise row before or after the goal contributes its whole block. -/
theorem goalTask_contains_premises {before goal after items}
    (task : goalTask before goal after = some items) {row : RoleRow} (member : row ∈ before ++ after)
    (premise : isPremise row.role = true) {declaration} (present : declaration ∈ row.row.declarations) :
    positive declaration ∈ items := by
  obtain ⟨_, formula, _, rfl⟩ := goalTask_shape task
  rcases List.mem_append.mp member with inBefore | inAfter
  · exact List.mem_append_left _ (selectBlock_contains inBefore premise present)
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (selectBlock_contains inAfter premise present))

/-- Every other item comes from a premise row; no other conjecture contributes. -/
theorem goalTask_other_items {before goal after items}
    (task : goalTask before goal after = some items) {item : SignedNumeric} (member : item ∈ items)
    (notNegative : isNegative item = false) :
    ∃ row ∈ before ++ after, isPremise row.role = true ∧
      ∃ declaration ∈ row.row.declarations, item = positive declaration := by
  obtain ⟨_, formula, _, rfl⟩ := goalTask_shape task
  rcases List.mem_append.mp member with inBefore | rest
  · obtain ⟨row, present, premise, declaration, inside, same⟩ := selectBlock_member inBefore
    exact ⟨row, List.mem_append_left _ present, premise, declaration, inside, same⟩
  · rcases List.mem_cons.mp rest with rfl | inAfter
    · simp [isNegative] at notNegative
    · obtain ⟨row, present, premise, declaration, inside, same⟩ := selectBlock_member inAfter
      exact ⟨row, List.mem_append_right _ present, premise, declaration, inside, same⟩

/-- The countermodel condition of RoleModels for this one goal. -/
theorem goalTask_models {values input before goal after items}
    (success : readSigned values = some input) (closed : Bytes.Closed values)
    (split : input.rows = before ++ goal :: after) (task : goalTask before goal after = some items)
    {D : Type} [Nonempty D] {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement input.functions input.predicates named numeric) :
    TaskModels numeric items ↔
      Roles.Countermodel (Bytes.sentence (D := D)) (Bytes.source values) goal.declaration named := by
  obtain ⟨isGoal, formula, shape, rfl⟩ := goalTask_shape task
  have goalMember : goal ∈ input.rows := by rw [split]; simp
  have inBefore : ∀ row ∈ before, row ∈ input.rows := by intro row member; rw [split]; simp [member]
  have inAfter : ∀ row ∈ after, row ∈ input.rows := by intro row member; rw [split]; simp [member]
  obtain ⟨body, _, bodyClosed⟩ := readSigned_row success closed goalMember
  rw [shape] at body
  obtain ⟨original, originalShape, rfl⟩ := readBody_fof body
  have originalClosed : original.Within [] := by
    simpa [Integration.BodyClosed, originalShape] using bodyClosed
  have formulaClosed : (original.encode input.functions input.predicates original.variables).Within [] := by
    simpa using Integration.encoded_formula_within original input.functions input.predicates
      original.variables [] originalClosed
  have goalModels := row_models success closed goalMember models
  rw [shape] at goalModels
  have goalSentence : (∀ valuation, (original.encode input.functions input.predicates
        original.variables).Holds numeric valuation) ↔
      Bytes.sentence named goal.row.original.body.formula := by
    rw [← goalModels]
    simp [NamedQuantified.NumericModels, NamedQuantified.NumericDeclaration.Models, formulaClosed]
  have negated : (SignedNumeric.fof false (original.encode input.functions input.predicates
        original.variables)).Holds numeric ↔ ¬ Bytes.sentence named goal.row.original.body.formula := by
    simp only [SignedNumeric.Holds, formulaClosed, true_and]
    rw [← closed_failure_iff numeric formulaClosed, goalSentence]
  obtain ⟨_, _, _, sources⟩ := readSigned_exact success
  rw [← sources, split, Roles.obligation_models]
  have premisesSplit : Roles.AllHold (Bytes.sentence (D := D))
      (Roles.premises ((before ++ goal :: after).map RoleRow.declaration)) named ↔
      (∀ row ∈ before, isPremise row.role = true → Bytes.sentence named row.row.original.body.formula) ∧
      (∀ row ∈ after, isPremise row.role = true → Bytes.sentence named row.row.original.body.formula) := by
    rw [show Roles.premises ((before ++ goal :: after).map RoleRow.declaration) =
        ((before ++ goal :: after).map RoleRow.declaration).filter
          (fun declaration => isPremise declaration.role) from rfl, allHold_select]
    simp only [List.forall_mem_append, List.forall_mem_cons, conjecture_not_premise isGoal,
      Bool.false_eq_true, false_implies, true_and]
  rw [premisesSplit, taskModels_append, taskModels_cons,
    selectBlock_models success closed isPremise models inBefore,
    selectBlock_models success closed isPremise models inAfter, negated]
  simp only [RoleRow.declaration]
  constructor
  · rintro ⟨first, goalFails, second⟩
    exact ⟨⟨first, second⟩, goalFails⟩
  · rintro ⟨⟨first, second⟩, goalFails⟩
    exact ⟨first, goalFails, second⟩

theorem goalTask_satisfiable_iff {values input before goal after items}
    (success : readSigned values = some input) (closed : Bytes.Closed values)
    (split : input.rows = before ++ goal :: after) (task : goalTask before goal after = some items) :
    TaskSatisfiable input items ↔ ∃ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Roles.Countermodel (Bytes.sentence (D := D)) (Bytes.source values) goal.declaration model := by
  constructor
  · rintro ⟨D, inhabited, model, holds⟩
    exact ⟨D, inhabited, Arity.toNamed model input.functions input.predicates,
      (goalTask_models success closed split task (model_toNamed model _ _)).mp holds⟩
  · rintro ⟨D, inhabited, model, countermodel⟩
    exact ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates,
      (goalTask_models success closed split task (model_toNumeric model _ _)).mpr countermodel⟩

/-- An unsatisfiable task proves the RoleModels entailment of that one original goal. -/
theorem goalTask_refuted_entails {values input before goal after items}
    (success : readSigned values = some input) (closed : Bytes.Closed values)
    (split : input.rows = before ++ goal :: after) (task : goalTask before goal after = some items)
    (refuted : ¬ TaskSatisfiable input items) :
    ∀ (D : Type) (_ : Nonempty D) (model : Source.Interpretation D),
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.premises (Bytes.source values)) model →
        Bytes.sentence model goal.declaration.original := by
  intro D inhabited model premisesHold
  apply Classical.byContradiction
  intro fails
  exact refuted ((goalTask_satisfiable_iff success closed split task).mpr
    ⟨D, inhabited, model, premisesHold, fails⟩)

theorem goal_row {values input} (success : readSigned values = some input)
    {goal : Roles.Declaration Name FullFof.Formula}
    (member : goal ∈ Roles.goals (Bytes.source values)) :
    ∃ before row after, input.rows = before ++ row :: after ∧ row.role = .conjecture ∧
      row.declaration = goal := by
  obtain ⟨_, _, _, sources⟩ := readSigned_exact success
  obtain ⟨present, role⟩ := Roles.goal_member.mp member
  rw [← sources] at present
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp present
  obtain ⟨before, after, split⟩ := List.append_of_mem rowMember
  exact ⟨before, row, after, split, role, rfl⟩

/-- Refuting every per-goal task proves original-byte entailment of every original conjecture. Each goal has its own task; none is negated jointly. -/
theorem tasks_refuted_entails {bytes maximum values input}
    (decoded : Bytes.decodeBytes bytes maximum = .ok values) (success : readSigned values = some input)
    (refuted : ∀ split ∈ splits input.rows, split.2.1.role = .conjecture →
      ∃ items, goalTask split.1 split.2.1 split.2.2 = some items ∧ ¬ TaskSatisfiable input items) :
    Bytes.BytesEntailsAll bytes maximum := by
  apply (Bytes.decode_entails_all decoded).mpr
  intro D inhabited goal member model premisesHold
  obtain ⟨before, row, after, split, role, rfl⟩ := goal_row success member
  obtain ⟨items, task, unsat⟩ := refuted (before, row, after) (mem_splits.mpr split) role
  exact goalTask_refuted_entails success (Bytes.decode_closed decoded) split task unsat D inhabited model
    premisesHold

/-- Conversely, entailment makes every constructed goal task unsatisfiable. -/
theorem entails_tasks_refuted {bytes maximum values input}
    (decoded : Bytes.decodeBytes bytes maximum = .ok values) (success : readSigned values = some input)
    (entails : Bytes.BytesEntailsAll bytes maximum) :
    ∀ split ∈ splits input.rows, ∀ items, goalTask split.1 split.2.1 split.2.2 = some items →
      ¬ TaskSatisfiable input items := by
  rintro ⟨before, goal, after⟩ member items task satisfiable
  have split := mem_splits.mp member
  obtain ⟨D, inhabited, model, premisesHold, fails⟩ :=
    (goalTask_satisfiable_iff success (Bytes.decode_closed decoded) split task).mp satisfiable
  have all := (Bytes.decode_entails_all decoded).mp entails D inhabited
  obtain ⟨_, _, _, sources⟩ := readSigned_exact success
  have goalMember : goal.declaration ∈ Roles.goals (Bytes.source values) := by
    rw [← sources, split]
    exact Roles.goal_member.mpr ⟨List.mem_map_of_mem (f := RoleRow.declaration) (by simp),
      (goalTask_shape task).1⟩
  exact (Roles.negative_holds _ _).mp fails (all goal.declaration goalMember model premisesHold)

theorem inputsTask_models {values input} (success : readSigned values = some input)
    (closed : Bytes.Closed values)
    {D : Type} {named : Source.Interpretation D} {numeric : Interpretation D}
    (models : ModelAgreement input.functions input.predicates named numeric) :
    TaskModels numeric (inputsTask input) ↔
      Roles.AllHold (Bytes.sentence (D := D)) (Roles.positiveInputs (Bytes.source values)) named := by
  obtain ⟨_, _, _, sources⟩ := readSigned_exact success
  rw [inputsTask, selectBlock_models success closed isPositiveInput models (fun row member => member),
    ← sources, show Roles.positiveInputs (input.rows.map RoleRow.declaration) =
      (input.rows.map RoleRow.declaration).filter
        (fun declaration => isPositiveInput declaration.role) from rfl, allHold_select]

/-- The no-goal mode is plain satisfiability of all accepted positive inputs. -/
theorem inputsTask_satisfiable_iff {bytes maximum values input}
    (decoded : Bytes.decodeBytes bytes maximum = .ok values) (success : readSigned values = some input)
    (noGoals : Roles.goals (Bytes.source values) = []) :
    TaskSatisfiable input (inputsTask input) ↔ Bytes.BytesInputsSatisfiable bytes maximum := by
  have closed := Bytes.decode_closed decoded
  rw [Bytes.decode_inputs_satisfiable decoded noGoals]
  constructor
  · rintro ⟨D, inhabited, model, holds⟩
    exact ⟨D, inhabited, Arity.toNamed model input.functions input.predicates,
      (inputsTask_models success closed (model_toNamed model _ _)).mp holds⟩
  · rintro ⟨D, inhabited, model, holds⟩
    exact ⟨D, inhabited, Arity.toNumeric model input.functions input.predicates,
      (inputsTask_models success closed (model_toNumeric model _ _)).mpr holds⟩

#print axioms Fang.TptpCandidate.Roles.Numeric.term_eval_agree
#print axioms Fang.TptpCandidate.Roles.Numeric.update_agree
#print axioms Fang.TptpCandidate.Roles.Numeric.holds_agree
#print axioms Fang.TptpCandidate.Roles.Numeric.closed_holds_independent
#print axioms Fang.TptpCandidate.Roles.Numeric.closed_failure_iff
#print axioms Fang.TptpCandidate.Roles.Numeric.named_failure_iff
#print axioms Fang.TptpCandidate.Roles.Numeric.readRoleRows_exact
#print axioms Fang.TptpCandidate.Roles.Numeric.readRoleRows_member
#print axioms Fang.TptpCandidate.Roles.Numeric.readSigned_exact
#print axioms Fang.TptpCandidate.Roles.Numeric.readSigned_row
#print axioms Fang.TptpCandidate.Roles.Numeric.row_models
#print axioms Fang.TptpCandidate.Roles.Numeric.readBody_fof
#print axioms Fang.TptpCandidate.Roles.Numeric.mem_splits
#print axioms Fang.TptpCandidate.Roles.Numeric.positive_holds
#print axioms Fang.TptpCandidate.Roles.Numeric.taskModels_append
#print axioms Fang.TptpCandidate.Roles.Numeric.taskModels_cons
#print axioms Fang.TptpCandidate.Roles.Numeric.selectBlock_models
#print axioms Fang.TptpCandidate.Roles.Numeric.allHold_select
#print axioms Fang.TptpCandidate.Roles.Numeric.conjecture_not_premise
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_shape
#print axioms Fang.TptpCandidate.Roles.Numeric.selectBlock_member
#print axioms Fang.TptpCandidate.Roles.Numeric.selectBlock_contains
#print axioms Fang.TptpCandidate.Roles.Numeric.positive_not_negative
#print axioms Fang.TptpCandidate.Roles.Numeric.selectBlock_no_negative
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_negative_items
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_contains_premises
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_other_items
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_models
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_satisfiable_iff
#print axioms Fang.TptpCandidate.Roles.Numeric.goalTask_refuted_entails
#print axioms Fang.TptpCandidate.Roles.Numeric.goal_row
#print axioms Fang.TptpCandidate.Roles.Numeric.tasks_refuted_entails
#print axioms Fang.TptpCandidate.Roles.Numeric.entails_tasks_refuted
#print axioms Fang.TptpCandidate.Roles.Numeric.inputsTask_models
#print axioms Fang.TptpCandidate.Roles.Numeric.inputsTask_satisfiable_iff

end Fang.TptpCandidate.Roles.Numeric
