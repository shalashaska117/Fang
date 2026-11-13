/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The statements of a finite model document in the TPTP finite interpretation format, and the proof that each one
   holds in the model. Every element gets a distinct-object name: an input distinct object names the element it
   denotes, and the other elements take one stem that begins no input object, followed by their index.
   `FiniteModel.named` adds those names to the model as constants. When `namesAgree` holds it agrees with the model on
   every function symbol of the input, so each input statement keeps its truth value (`named_holds_iff`). Each cell
   statement states the value the named model gives that cell, so `documentRows_hold` needs no fact about how the
   tables are stored. A table with more cells than `Layout.cells` is written as one value and the cells that differ
   from it, when at most `Layout.cells` of them differ. Every input symbol other than a distinct object gets its rows
   once (`describedFunctions_nodup`, `mem_describedFunctions`). This module imports no extracted code. -/
import ModelSemantics

namespace Fang.TptpCandidate.FullFof.Model

open NamedQuantified (update)

/-! Symbols in first-occurrence order, each once. -/

def firstOccurrences : Std.HashSet (String × Nat) → List (String × Nat) → List (String × Nat)
  | _, [] => []
  | seen, symbol :: rest =>
    if seen.contains symbol then firstOccurrences seen rest
    else symbol :: firstOccurrences (seen.insert symbol) rest

theorem firstOccurrences_mem : ∀ (seen : Std.HashSet (String × Nat)) (symbols : List (String × Nat))
    (symbol : String × Nat), symbol ∈ firstOccurrences seen symbols ↔ symbol ∈ symbols ∧ seen.contains symbol = false
  | _, [], _ => by simp [firstOccurrences]
  | seen, first :: rest, symbol => by
    unfold firstOccurrences
    by_cases present : seen.contains first = true
    · simp only [present, ↓reduceIte, firstOccurrences_mem seen rest symbol, List.mem_cons]
      constructor
      · intro found
        exact ⟨Or.inr found.1, found.2⟩
      · intro found
        rcases found with ⟨same | member, absent⟩
        · subst same
          rw [present] at absent
          cases absent
        · exact ⟨member, absent⟩
    · simp only [present, Bool.false_eq_true, ↓reduceIte, List.mem_cons, firstOccurrences_mem _ rest symbol,
        Std.HashSet.contains_insert]
      by_cases same : symbol = first
      · subst same
        simp only [Bool.not_eq_true] at present
        simp [present]
      · have different : (first == symbol) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
        simp [same, different]

theorem firstOccurrences_nodup : ∀ (seen : Std.HashSet (String × Nat)) (symbols : List (String × Nat)),
    (firstOccurrences seen symbols).Nodup
  | _, [] => List.nodup_nil
  | seen, first :: rest => by
    unfold firstOccurrences
    split
    · exact firstOccurrences_nodup seen rest
    · refine List.nodup_cons.mpr ⟨?_, firstOccurrences_nodup _ rest⟩
      intro member
      have absent := ((firstOccurrences_mem _ rest first).mp member).2
      simp [Std.HashSet.contains_insert] at absent

/-- A name the decoders give a distinct object: its content after a NUL byte, which no other name contains. -/
def isObjectName (name : String) : Bool := name.toList.head? == some '\x00'

/-- Every function symbol of the statements, distinct objects included. -/
def allFunctions (statements : List Formula) : List (String × Nat) :=
  firstOccurrences ∅ (statements.flatMap Formula.functions)

/-- The function symbols a document describes: those of the statements other than distinct objects, which name their
    own elements. -/
def describedFunctions (statements : List Formula) : List (String × Nat) :=
  firstOccurrences ∅ ((statements.flatMap Formula.functions).filter fun symbol => !isObjectName symbol.1)

def describedPredicates (statements : List Formula) : List (String × Nat) :=
  firstOccurrences ∅ (statements.flatMap Formula.predicates)

theorem mem_allFunctions {statements : List Formula} {symbol : String × Nat} :
    symbol ∈ allFunctions statements ↔ ∃ formula ∈ statements, symbol ∈ formula.functions := by
  simp [allFunctions, firstOccurrences_mem]

theorem mem_describedFunctions {statements : List Formula} {symbol : String × Nat} :
    symbol ∈ describedFunctions statements ↔
      (∃ formula ∈ statements, symbol ∈ formula.functions) ∧ isObjectName symbol.1 = false := by
  simp [describedFunctions, firstOccurrences_mem]

theorem mem_describedPredicates {statements : List Formula} {symbol : String × Nat} :
    symbol ∈ describedPredicates statements ↔ ∃ formula ∈ statements, symbol ∈ formula.predicates := by
  simp [describedPredicates, firstOccurrences_mem]

theorem describedFunctions_nodup (statements : List Formula) : (describedFunctions statements).Nodup :=
  firstOccurrences_nodup _ _

theorem describedPredicates_nodup (statements : List Formula) : (describedPredicates statements).Nodup :=
  firstOccurrences_nodup _ _

/-! Element names. -/

def objectNamed (content : String) : String := String.ofList ('\x00' :: content.toList)

/-- `e`, then `fang_e`, `fang_fang_e` and so on, the first that begins no object's content. Each object begins with at
    most one of these, so one more candidate than there are objects always finds one. -/
def freshStem (objects : List String) : Nat → String → Option String
  | 0, _ => none
  | fuel + 1, stem =>
    if objects.any (fun object => stem.toList.isPrefixOf (object.toList.drop 1)) then
      freshStem objects fuel ("fang_" ++ stem)
    else some stem

/-- The input object that denotes the element, or the stem followed by the element's index. -/
def elementName (model : FiniteModel) (objects : List String) (stem : String) (index : Nat) : String :=
  match objects.find? (fun object => (model.function object []).val == index) with
  | some object => object
  | none => objectNamed (stem ++ toString index)

def elementNames (model : FiniteModel) (objects : List String) (stem : String) : List String :=
  (List.range (model.size + 1)).map (elementName model objects stem)

/-! The model with its element names as constants. -/

def insertNames : Nat → List String → Std.HashMap (String × Nat) Table → Std.HashMap (String × Nat) Table
  | _, [], tables => tables
  | index, name :: rest, tables => insertNames (index + 1) rest (tables.insert (name, 0) (.dense #[index]))

/-- The model where the name at position `index` is a constant for the element `index`. Reducible, so that its
    elements are the model's own. -/
@[reducible] def FiniteModel.named (model : FiniteModel) (names : List String) : FiniteModel where
  size := model.size
  functions := insertNames 0 names model.functions
  predicates := model.predicates

theorem insertNames_other : ∀ (names : List String) (index : Nat) (tables : Std.HashMap (String × Nat) Table)
    (key : String × Nat), (∀ name ∈ names, (name, 0) ≠ key) → (insertNames index names tables)[key]? = tables[key]?
  | [], _, _, _, _ => rfl
  | name :: rest, index, tables, key, absent => by
    simp only [insertNames]
    rw [insertNames_other rest (index + 1) _ key (fun other member => absent other (List.mem_cons_of_mem _ member)),
      Std.HashMap.getElem?_insert]
    have different : ((name, 0) == key) = false := beq_eq_false_iff_ne.mpr (absent name (by simp))
    simp [different]

theorem insertNames_at : ∀ (names : List String) (index : Nat) (tables : Std.HashMap (String × Nat) Table)
    (position : Nat) (inside : position < names.length), names.Nodup →
    (insertNames index names tables)[(names[position], 0)]? = some (.dense #[index + position])
  | [], _, _, _, inside, _ => absurd inside (by simp)
  | name :: rest, index, tables, 0, _, distinct => by
    simp only [insertNames, List.getElem_cons_zero, Nat.add_zero]
    have fresh : name ∉ rest := (List.nodup_cons.mp distinct).1
    rw [insertNames_other rest (index + 1) _ (name, 0)
      (fun other member same => fresh ((Prod.mk.inj same).1 ▸ member))]
    simp
  | name :: rest, index, tables, position + 1, inside, distinct => by
    simp only [insertNames, List.getElem_cons_succ]
    rw [insertNames_at rest (index + 1) _ position (by simpa using inside) (List.nodup_cons.mp distinct).2]
    have shifted : index + 1 + position = index + (position + 1) := by omega
    rw [shifted]

def elementTerm (names : List String) (index : Nat) : Source.Term := .app (names.getD index "") []

theorem named_element {model : FiniteModel} {names : List String} (length : names.length = model.size + 1)
    (distinct : names.Nodup) (element : model.Element) :
    (model.named names).function (names.getD element.val "") [] = element := by
  have inside : element.val < names.length := by rw [length]; exact element.isLt
  have lookup := insertNames_at names 0 model.functions element.val inside distinct
  have getD : names.getD element.val "" = names[element.val] := by
    simp [List.getD_eq_getElem?_getD, inside]
  apply Fin.ext
  simp only [FiniteModel.function, FiniteModel.named, List.length_nil, getD, lookup, Table.read, List.map_nil,
    cellIndex, List.foldl_nil, FiniteModel.element]
  simp [Nat.mod_eq_of_lt element.isLt]

theorem elementTerm_eval {model : FiniteModel} {names : List String} (length : names.length = model.size + 1)
    (distinct : names.Nodup) (element : model.Element) (valuation : String → model.Element) :
    (elementTerm names element.val).eval (model.named names).interpretation valuation = element := by
  simp only [elementTerm, Source.Term.eval, List.map_nil]
  exact named_element length distinct element

/-! Agreement with the model on the input's function symbols. -/

/-- Each name that is also a nullary function symbol of the input already denotes its element in the model. -/
def namesAgree (model : FiniteModel) (names : List String) (functions : List (String × Nat)) : Bool :=
  (List.range names.length).all fun position =>
    !(functions.contains (names.getD position "", 0)) || (model.function (names.getD position "") []).val == position

theorem named_function_agree {model : FiniteModel} {names : List String} {functions : List (String × Nat)}
    (length : names.length = model.size + 1) (distinct : names.Nodup) (agree : namesAgree model names functions = true)
    {name : String} {arity : Nat} (member : (name, arity) ∈ functions) (arguments : List model.Element)
    (count : arguments.length = arity) :
    (model.named names).function name arguments = model.function name arguments := by
  by_cases named : ∃ position, ∃ inside : position < names.length, names[position] = name ∧ arity = 0
  · obtain ⟨position, inside, same, zero⟩ := named
    have empty : arguments = [] := List.eq_nil_of_length_eq_zero (count.trans zero)
    subst empty zero
    have check := List.all_eq_true.mp agree position (List.mem_range.mpr inside)
    have getD : names.getD position "" = names[position] := by simp [List.getD_eq_getElem?_getD, inside]
    simp only [getD, same] at check
    have contained : functions.contains (name, 0) = true := List.contains_iff_mem.mpr member
    simp only [contained, Bool.not_true, Bool.false_or, beq_iff_eq] at check
    have lookup := insertNames_at names 0 model.functions position inside distinct
    rw [same] at lookup
    apply Fin.ext
    rw [check]
    simp only [FiniteModel.function, FiniteModel.named, List.length_nil, lookup, Table.read, List.map_nil, cellIndex,
      List.foldl_nil, FiniteModel.element]
    have small : position < model.size + 1 := length ▸ inside
    simp [Nat.mod_eq_of_lt small]
  · have other : ∀ candidate ∈ names, (candidate, 0) ≠ (name, arguments.length) := by
      intro candidate member same
      obtain ⟨position, inside, found⟩ := List.getElem_of_mem member
      exact named ⟨position, inside, found.trans (Prod.mk.inj same).1, count ▸ (Prod.mk.inj same).2.symm⟩
    simp only [FiniteModel.function, FiniteModel.named]
    rw [insertNames_other names 0 model.functions _ other]
    rfl

/-! Agreement on the function symbols of a formula keeps its truth value. -/

theorem eval_functions_agree {D : Type} {left right : Source.Interpretation D} (valuation : String → D)
    (term : Source.Term)
    (same : ∀ symbol ∈ Arity.termFunctions term, ∀ arguments : List D, arguments.length = symbol.2 →
      left.function symbol.1 arguments = right.function symbol.1 arguments) :
    term.eval left valuation = term.eval right valuation := by
  cases term with
  | var name => simp only [Source.Term.eval]
  | app symbol arguments =>
    simp only [Source.Term.eval]
    have inner : arguments.map (Source.Term.eval left valuation) = arguments.map (Source.Term.eval right valuation) :=
      List.map_congr_left fun child member => eval_functions_agree valuation child fun found inside =>
        same found (by
          simp only [Arity.termFunctions, List.mem_cons, List.mem_flatMap]
          exact Or.inr ⟨child, member, inside⟩)
    rw [inner]
    exact same (symbol, arguments.length) (by simp [Arity.termFunctions]) _ (by simp)
termination_by sizeOf term

theorem holds_functions_agree {D : Type} {left right : Source.Interpretation D}
    (predicates : left.predicate = right.predicate) (formula : Formula)
    (same : ∀ symbol ∈ formula.functions, ∀ arguments : List D, arguments.length = symbol.2 →
      left.function symbol.1 arguments = right.function symbol.1 arguments) :
    ∀ valuation, formula.Holds left valuation ↔ formula.Holds right valuation := by
  induction formula with
  | atom name arguments =>
    intro valuation
    have values : arguments.map (Source.Term.eval left valuation) =
        arguments.map (Source.Term.eval right valuation) :=
      List.map_congr_left fun term member => eval_functions_agree valuation term fun symbol inside =>
        same symbol (by
          simp only [Formula.functions, List.mem_flatMap]
          exact ⟨term, member, inside⟩)
    simp only [Formula.Holds, values, predicates]
  | equal first second =>
    intro valuation
    have firstSame := eval_functions_agree valuation first fun symbol inside =>
      same symbol (by simp only [Formula.functions, List.mem_append]; exact Or.inl inside)
    have secondSame := eval_functions_agree valuation second fun symbol inside =>
      same symbol (by simp only [Formula.functions, List.mem_append]; exact Or.inr inside)
    simp only [Formula.Holds, firstSame, secondSame]
  | truth => intro _; exact Iff.rfl
  | falsity => intro _; exact Iff.rfl
  | neg body ih =>
    intro valuation
    simp only [Formula.Holds]
    exact not_congr (ih same valuation)
  | pair operator first second ihFirst ihSecond =>
    intro valuation
    simp only [Formula.Holds]
    rw [ihFirst (fun symbol inside => same symbol (by simp only [Formula.functions, List.mem_append]; exact Or.inl inside))
        valuation,
      ihSecond (fun symbol inside => same symbol (by simp only [Formula.functions, List.mem_append]; exact Or.inr inside))
        valuation]
  | all name body ih =>
    intro valuation
    simp only [Formula.Holds]
    exact forall_congr' fun value => ih same _
  | ex name body ih =>
    intro valuation
    simp only [Formula.Holds]
    exact exists_congr fun value => ih same _

/-- With agreeing names, every input statement has the same truth value in the named model. -/
theorem named_holds_iff {model : FiniteModel} {names : List String} {statements : List Formula}
    (length : names.length = model.size + 1) (distinct : names.Nodup)
    (agree : namesAgree model names (allFunctions statements) = true) {formula : Formula}
    (member : formula ∈ statements) (valuation : String → model.Element) :
    formula.Holds (model.named names).interpretation valuation ↔ formula.Holds model.interpretation valuation := by
  apply holds_functions_agree (left := (model.named names).interpretation) (right := model.interpretation) rfl formula
  intro symbol inside arguments count
  exact named_function_agree length distinct agree (mem_allFunctions.mpr ⟨formula, member, inside⟩) arguments count

/-! Argument lists. -/

/-- Every argument list of `arity` elements after `front` that `keep` accepts, in row-major order, first argument most
    significant. -/
def tuples (model : FiniteModel) (keep : List model.Element → Bool) :
    Nat → List model.Element → List (List model.Element)
  | 0, front => if keep front then [front] else []
  | arity + 1, front => (List.finRange (model.size + 1)).flatMap fun value => tuples model keep arity (front ++ [value])

theorem tuples_complete (model : FiniteModel) (keep : List model.Element → Bool) :
    ∀ (arity : Nat) (front rest : List model.Element), rest.length = arity → keep (front ++ rest) = true →
      front ++ rest ∈ tuples model keep arity front
  | 0, front, [], _, kept => by
    simp only [List.append_nil] at kept ⊢
    simp [tuples, kept]
  | 0, _, _ :: _, count, _ => by simp at count
  | _ + 1, _, [], count, _ => by simp at count
  | arity + 1, front, value :: rest, count, kept => by
    simp only [tuples, List.mem_flatMap]
    refine ⟨value, List.mem_finRange value, ?_⟩
    have regroup : front ++ value :: rest = (front ++ [value]) ++ rest := by simp
    rw [regroup] at kept ⊢
    exact tuples_complete model keep arity (front ++ [value]) rest (by simpa using count) kept

/-! Chains and balanced trees of one connective. -/

/-- `first op second op ...`, nested to the left as the decoders read it. -/
def chainOf (operator : Binary) (first : Formula) (rest : List Formula) : Formula :=
  rest.foldl (Formula.pair operator) first

def chainAll (operator : Binary) (empty : Formula) : List Formula → Formula
  | [] => empty
  | first :: rest => chainOf operator first rest

/-- At most 16 leaves as one chain; more split in halves, so the nesting grows with the logarithm of their number.
    The fuel only bounds the recursion: when it runs out the rest is one chain, which holds just the same. -/
def treeWith (operator : Binary) (empty : Formula) : Nat → List Formula → Formula
  | 0, leaves => chainAll operator empty leaves
  | fuel + 1, leaves =>
    if leaves.length ≤ 16 then chainAll operator empty leaves
    else .pair operator (treeWith operator empty fuel (leaves.take (leaves.length / 2)))
      (treeWith operator empty fuel (leaves.drop (leaves.length / 2)))

def treeOf (operator : Binary) (empty : Formula) (leaves : List Formula) : Formula :=
  treeWith operator empty leaves.length leaves

section Trees
variable {D : Type} (model : Source.Interpretation D) (valuation : String → D)

theorem chainOf_conj : ∀ (first : Formula) (rest : List Formula), first.Holds model valuation →
    (∀ leaf ∈ rest, leaf.Holds model valuation) → (chainOf .conj first rest).Holds model valuation
  | _, [], holds, _ => holds
  | first, next :: rest, holds, others => by
    show (chainOf .conj (.pair .conj first next) rest).Holds model valuation
    apply chainOf_conj
    · simp only [Formula.Holds, Binary.meaning]
      exact ⟨holds, others next (by simp)⟩
    · exact fun leaf member => others leaf (List.mem_cons_of_mem _ member)

theorem chainOf_disj : ∀ (first : Formula) (rest : List Formula),
    (first.Holds model valuation ∨ ∃ leaf ∈ rest, leaf.Holds model valuation) →
      (chainOf .disj first rest).Holds model valuation
  | _, [], holds => holds.elim id fun ⟨_, member, _⟩ => absurd member (by simp)
  | first, next :: rest, holds => by
    show (chainOf .disj (.pair .disj first next) rest).Holds model valuation
    apply chainOf_disj
    rcases holds with here | ⟨leaf, member, there⟩
    · left
      simp only [Formula.Holds, Binary.meaning]
      exact Or.inl here
    · rcases List.mem_cons.mp member with same | later
      · subst same
        left
        simp only [Formula.Holds, Binary.meaning]
        exact Or.inr there
      · exact Or.inr ⟨leaf, later, there⟩

theorem chainAll_conj (leaves : List Formula) (all : ∀ leaf ∈ leaves, leaf.Holds model valuation) :
    (chainAll .conj .truth leaves).Holds model valuation := by
  cases leaves with
  | nil => trivial
  | cons first rest =>
    exact chainOf_conj model valuation first rest (all first (by simp))
      (fun leaf member => all leaf (List.mem_cons_of_mem _ member))

theorem chainAll_disj (leaves : List Formula) (found : ∃ leaf ∈ leaves, leaf.Holds model valuation) :
    (chainAll .disj .falsity leaves).Holds model valuation := by
  cases leaves with
  | nil => obtain ⟨_, member, _⟩ := found; cases member
  | cons first rest =>
    obtain ⟨leaf, member, holds⟩ := found
    apply chainOf_disj model valuation first rest
    rcases List.mem_cons.mp member with same | later
    · subst same
      exact Or.inl holds
    · exact Or.inr ⟨leaf, later, holds⟩

theorem treeWith_conj : ∀ (fuel : Nat) (leaves : List Formula), (∀ leaf ∈ leaves, leaf.Holds model valuation) →
    (treeWith .conj .truth fuel leaves).Holds model valuation
  | 0, leaves, all => chainAll_conj model valuation leaves all
  | fuel + 1, leaves, all => by
    unfold treeWith
    split
    · exact chainAll_conj model valuation leaves all
    · simp only [Formula.Holds, Binary.meaning]
      exact ⟨treeWith_conj fuel _ (fun leaf member => all leaf (List.mem_of_mem_take member)),
        treeWith_conj fuel _ (fun leaf member => all leaf (List.mem_of_mem_drop member))⟩

theorem treeWith_disj : ∀ (fuel : Nat) (leaves : List Formula), (∃ leaf ∈ leaves, leaf.Holds model valuation) →
    (treeWith .disj .falsity fuel leaves).Holds model valuation
  | 0, leaves, found => chainAll_disj model valuation leaves found
  | fuel + 1, leaves, found => by
    unfold treeWith
    split
    · exact chainAll_disj model valuation leaves found
    · obtain ⟨leaf, member, holds⟩ := found
      simp only [Formula.Holds, Binary.meaning]
      rw [← List.take_append_drop (leaves.length / 2) leaves, List.mem_append] at member
      rcases member with early | late
      · exact Or.inl (treeWith_disj fuel _ ⟨leaf, early, holds⟩)
      · exact Or.inr (treeWith_disj fuel _ ⟨leaf, late, holds⟩)

theorem treeOf_conj (leaves : List Formula) (all : ∀ leaf ∈ leaves, leaf.Holds model valuation) :
    (treeOf .conj .truth leaves).Holds model valuation :=
  treeWith_conj model valuation leaves.length leaves all

theorem treeOf_disj (leaves : List Formula) (found : ∃ leaf ∈ leaves, leaf.Holds model valuation) :
    (treeOf .disj .falsity leaves).Holds model valuation :=
  treeWith_disj model valuation leaves.length leaves found

end Trees

/-! Statements. -/

def variablesFor (arity : Nat) : List String := (List.range arity).map fun index => "X" ++ toString (index + 1)

theorem variablesFor_length (arity : Nat) : (variablesFor arity).length = arity := by simp [variablesFor]

def closeAll (binders : List String) (body : Formula) : Formula := binders.foldr Formula.all body

theorem closeAll_holds {D : Type} (model : Source.Interpretation D) (binders : List String) (body : Formula)
    (holds : ∀ valuation, body.Holds model valuation) :
    ∀ valuation, (closeAll binders body).Holds model valuation := by
  induction binders with
  | nil => exact holds
  | cons name rest ih =>
    intro valuation
    simp only [closeAll, List.foldr_cons, Formula.Holds] at ih ⊢
    intro value
    exact ih _

def argumentsOf {size : Nat} (names : List String) (cells : List (Fin size)) : List Source.Term :=
  cells.map fun cell => elementTerm names cell.val

/-- `f(a,...) = v` for the value `v` the named model gives the cell. -/
def functionCell (model : FiniteModel) (names : List String) (symbol : String) (cells : List model.Element) : Formula :=
  .equal (.app symbol (argumentsOf names cells)) (elementTerm names ((model.named names).function symbol cells).val)

/-- `p(a,...)` or `~ p(a,...)` as the named model gives the cell. -/
def predicateCell (model : FiniteModel) (names : List String) (symbol : String) (cells : List model.Element) :
    Formula :=
  if (model.named names).predicate symbol cells then .atom symbol (argumentsOf names cells)
  else .neg (.atom symbol (argumentsOf names cells))

section Cells
variable {model : FiniteModel} {names : List String} (length : names.length = model.size + 1) (distinct : names.Nodup)
include length distinct

theorem argumentsOf_eval (cells : List model.Element) (valuation : String → model.Element) :
    (argumentsOf names cells).map (Source.Term.eval (model.named names).interpretation valuation) = cells := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    simp only [argumentsOf, List.map_cons] at ih ⊢
    rw [elementTerm_eval length distinct, ih]

theorem functionCell_holds (symbol : String) (cells : List model.Element) (valuation : String → model.Element) :
    (functionCell model names symbol cells).Holds (model.named names).interpretation valuation := by
  simp only [functionCell, Formula.Holds]
  rw [elementTerm_eval length distinct]
  simp only [Source.Term.eval]
  rw [argumentsOf_eval length distinct]
  rfl

theorem predicateCell_holds (symbol : String) (cells : List model.Element) (valuation : String → model.Element) :
    (predicateCell model names symbol cells).Holds (model.named names).interpretation valuation := by
  unfold predicateCell
  split
  · rename_i value
    simp only [Formula.Holds]
    rw [argumentsOf_eval length distinct]
    exact value
  · rename_i value
    simp only [Formula.Holds]
    rw [argumentsOf_eval length distinct]
    exact value

end Cells

/-- `X1 = a1`, `X2 = a2`, ... for one argument list. -/
def bindings {size : Nat} (names : List String) : List String → List (Fin size) → List Formula
  | binder :: binders, cell :: cells => .equal (.var binder) (elementTerm names cell.val) :: bindings names binders cells
  | _, _ => []

def tupleFormula {size : Nat} (names : List String) (binders : List String) (cells : List (Fin size)) : Formula :=
  treeOf .conj .truth (bindings names binders cells)

theorem bindings_hold {model : FiniteModel} {names : List String} (length : names.length = model.size + 1)
    (distinct : names.Nodup) (valuation : String → model.Element) :
    ∀ (binders : List String), ∀ leaf ∈ bindings names binders (binders.map valuation),
      leaf.Holds (model.named names).interpretation valuation
  | [], leaf, member => by simp [bindings] at member
  | binder :: rest, leaf, member => by
    simp only [List.map_cons, bindings, List.mem_cons] at member
    rcases member with same | later
    · subst same
      simp only [Formula.Holds]
      rw [elementTerm_eval length distinct]
      simp only [Source.Term.eval]
    · exact bindings_hold length distinct valuation rest leaf later

/-- `! [X1,...] : ( fallback | the arguments are one of the exceptions )`, or the fallback alone without exceptions. -/
def defaultFormula {size : Nat} (names : List String) (binders : List String) (fallback : Formula)
    (exceptions : List (List (Fin size))) : Formula :=
  closeAll binders (match exceptions with
    | [] => fallback
    | _ :: _ => .pair .disj fallback (treeOf .disj .falsity (exceptions.map (tupleFormula names binders))))

theorem defaultFormula_holds {model : FiniteModel} {names : List String} (length : names.length = model.size + 1)
    (distinct : names.Nodup) (binders : List String) (fallback : Formula) (exceptions : List (List model.Element))
    (covered : ∀ valuation : String → model.Element,
      fallback.Holds (model.named names).interpretation valuation ∨ binders.map valuation ∈ exceptions) :
    ∀ valuation, (defaultFormula names binders fallback exceptions).Holds (model.named names).interpretation
      valuation := by
  apply closeAll_holds
  intro valuation
  have tupleHolds : (tupleFormula names binders (binders.map valuation)).Holds (model.named names).interpretation
      valuation := treeOf_conj _ _ _ (bindings_hold length distinct valuation binders)
  cases exceptions with
  | nil =>
    rcases covered valuation with here | member
    · exact here
    · cases member
  | cons first rest =>
    simp only [Formula.Holds, Binary.meaning]
    rcases covered valuation with here | member
    · exact Or.inl here
    · exact Or.inr (treeOf_disj _ _ _ ⟨_, List.mem_map_of_mem member, tupleHolds⟩)

/-! Rows. -/

/-- One statement of the document: its name, its role in the finite interpretation format and its formula. -/
structure Row where
  label : String
  role : String
  formula : Formula

/-- When a table is written cell by cell. The theorems hold for every value. -/
structure Layout where
  /-- Tables with at most this many cells, and tables with at most this many exceptions, are written in full. -/
  cells : Nat
  /-- Larger tables are not enumerated. -/
  enumeration : Nat
  /-- Above `cells`, a table with too many exceptions is written cell by cell up to this size. -/
  dense : Nat

def defaultLayout : Layout where
  cells := 4096
  enumeration := 4194304
  dense := 65536

/-- The most frequent stored value of a table, taken as its default; the theorems do not depend on it. -/
def mostFrequent (base : Nat) (cells : Array Nat) : Nat :=
  let counts := cells.foldl (fun counts value => counts.modify value (· + 1)) (Array.replicate base 0)
  (List.range base).foldl (fun best index => if counts.getD index 0 > counts.getD best 0 then index else best) 0

def tableDefault (base : Nat) : Option Table → Nat
  | some (.sparse fallback _) => fallback
  | some (.dense cells) => mostFrequent base cells
  | none => 0

def domainFormula (model : FiniteModel) (names : List String) : Formula :=
  .all "X" (treeOf .disj .falsity ((List.finRange (model.size + 1)).map fun element =>
    .equal (.var "X") (elementTerm names element.val)))

def functionFallback (names : List String) (symbol : String) (arity : Nat) (value : Nat) : Formula :=
  .equal (.app symbol ((variablesFor arity).map Source.Term.var)) (elementTerm names value)

def predicateFallback (symbol : String) (arity : Nat) (value : Bool) : Formula :=
  if value then .atom symbol ((variablesFor arity).map Source.Term.var)
  else .neg (.atom symbol ((variablesFor arity).map Source.Term.var))

def functionDense (model : FiniteModel) (names : List String) (symbol : String) (arity : Nat) (label : String) :
    List Row :=
  [⟨label, "fi_functors", treeOf .conj .truth ((tuples model (fun _ => true) arity []).map
    (functionCell model names symbol))⟩]

def predicateDense (model : FiniteModel) (names : List String) (symbol : String) (arity : Nat) (label : String) :
    List Row :=
  [⟨label, "fi_predicates", treeOf .conj .truth ((tuples model (fun _ => true) arity []).map
    (predicateCell model names symbol))⟩]

def functionRows (layout : Layout) (model : FiniteModel) (names : List String) (symbol : String) (arity : Nat)
    (label : String) : Except String (List Row) :=
  if (model.size + 1) ^ arity ≤ layout.cells then .ok (functionDense model names symbol arity label)
  else if (model.size + 1) ^ arity > layout.enumeration then .error "resource.export.table"
  else
    let value := model.element (tableDefault (model.size + 1) model.functions[(symbol, arity)]?)
    let exceptions := tuples model (fun cells => (model.named names).function symbol cells != value) arity []
    if exceptions.length ≤ layout.cells then
      .ok ((match exceptions with
          | [] => []
          | _ :: _ => [⟨label, "fi_functors", treeOf .conj .truth (exceptions.map (functionCell model names symbol))⟩]) ++
        [⟨label ++ "_default", "fi_functors",
          defaultFormula names (variablesFor arity) (functionFallback names symbol arity value.val) exceptions⟩])
    else if (model.size + 1) ^ arity ≤ layout.dense then .ok (functionDense model names symbol arity label)
    else .error "resource.export.table"

def predicateRows (layout : Layout) (model : FiniteModel) (names : List String) (symbol : String) (arity : Nat)
    (label : String) : Except String (List Row) :=
  if (model.size + 1) ^ arity ≤ layout.cells then .ok (predicateDense model names symbol arity label)
  else if (model.size + 1) ^ arity > layout.enumeration then .error "resource.export.table"
  else
    let value := tableDefault 2 model.predicates[(symbol, arity)]? != 0
    let exceptions := tuples model (fun cells => (model.named names).predicate symbol cells != value) arity []
    if exceptions.length ≤ layout.cells then
      .ok ((match exceptions with
          | [] => []
          | _ :: _ => [⟨label, "fi_predicates", treeOf .conj .truth (exceptions.map (predicateCell model names symbol))⟩]) ++
        [⟨label ++ "_default", "fi_predicates",
          defaultFormula names (variablesFor arity) (predicateFallback symbol arity value) exceptions⟩])
    else if (model.size + 1) ^ arity ≤ layout.dense then .ok (predicateDense model names symbol arity label)
    else .error "resource.export.table"

def symbolRows (make : String → Nat → String → Except String (List Row)) (kind : String) :
    Nat → List (String × Nat) → Except String (List Row)
  | _, [] => .ok []
  | position, (symbol, arity) :: rest =>
    match make symbol arity (kind ++ toString position) with
    | .error problem => .error problem
    | .ok first =>
      match symbolRows make kind (position + 1) rest with
      | .error problem => .error problem
      | .ok more => .ok (first ++ more)

/-- The domain statement, then the rows of each function symbol, then those of each predicate symbol. -/
def documentRows (layout : Layout) (model : FiniteModel) (names : List String)
    (functions predicates : List (String × Nat)) : Except String (List Row) :=
  match symbolRows (functionRows layout model names) "fang_function_" 1 functions with
  | .error problem => .error problem
  | .ok functionPart =>
    match symbolRows (predicateRows layout model names) "fang_predicate_" 1 predicates with
    | .error problem => .error problem
    | .ok predicatePart =>
      .ok (⟨"fang_domain", "fi_domain", domainFormula model names⟩ :: (functionPart ++ predicatePart))

/-! Every row holds in the named model. -/

theorem symbolRows_hold {P : Row → Prop} {make : String → Nat → String → Except String (List Row)} {kind : String}
    (each : ∀ symbol arity label rows, make symbol arity label = .ok rows → ∀ row ∈ rows, P row) :
    ∀ (position : Nat) (symbols : List (String × Nat)) (rows : List Row), symbolRows make kind position symbols = .ok rows →
      ∀ row ∈ rows, P row
  | _, [], rows, built => by
    simp only [symbolRows, Except.ok.injEq] at built
    subst built
    intro row member
    cases member
  | position, (symbol, arity) :: rest, rows, built => by
    simp only [symbolRows] at built
    split at built
    · cases built
    · rename_i first made
      split at built
      · cases built
      · rename_i more later
        simp only [Except.ok.injEq] at built
        subst built
        intro row member
        rcases List.mem_append.mp member with early | late
        · exact each symbol arity _ first made row early
        · exact symbolRows_hold each (position + 1) rest more later row late

section Hold
variable {model : FiniteModel} {names : List String} (length : names.length = model.size + 1) (distinct : names.Nodup)
include length distinct

theorem domainFormula_holds (valuation : String → model.Element) :
    (domainFormula model names).Holds (model.named names).interpretation valuation := by
  simp only [domainFormula, Formula.Holds]
  intro value
  apply treeOf_disj
  refine ⟨.equal (.var "X") (elementTerm names value.val), List.mem_map_of_mem (List.mem_finRange value), ?_⟩
  simp only [Formula.Holds, Source.Term.eval]
  rw [elementTerm_eval length distinct]
  simp [update]

theorem functionRows_hold {layout : Layout} {symbol : String} {arity : Nat} {label : String} {rows : List Row}
    (built : functionRows layout model names symbol arity label = .ok rows) :
    ∀ row ∈ rows, ∀ valuation, row.formula.Holds (model.named names).interpretation valuation := by
  have dense : ∀ row ∈ functionDense model names symbol arity label, ∀ valuation,
      row.formula.Holds (model.named names).interpretation valuation := by
    intro row member valuation
    simp only [functionDense, List.mem_singleton] at member
    subst member
    apply treeOf_conj
    intro leaf inside
    obtain ⟨cells, _, rfl⟩ := List.mem_map.mp inside
    exact functionCell_holds length distinct symbol cells valuation
  unfold functionRows at built
  split at built
  · cases built
    exact dense
  · split at built
    · cases built
    · dsimp only at built
      split at built
      · cases built
        intro row member valuation
        rcases List.mem_append.mp member with early | late
        · split at early
          · cases early
          · simp only [List.mem_singleton] at early
            subst early
            apply treeOf_conj
            intro leaf inside
            obtain ⟨cells, _, rfl⟩ := List.mem_map.mp inside
            exact functionCell_holds length distinct symbol cells valuation
        · simp only [List.mem_singleton] at late
          subst late
          apply defaultFormula_holds length distinct
          intro assignment
          have arguments : ((variablesFor arity).map Source.Term.var).map
              (Source.Term.eval (model.named names).interpretation assignment) = (variablesFor arity).map assignment := by
            simp only [List.map_map, Function.comp_def, Source.Term.eval]
          by_cases same : (model.named names).function symbol ((variablesFor arity).map assignment) =
              model.element (tableDefault (model.size + 1) model.functions[(symbol, arity)]?)
          · left
            simp only [functionFallback, Formula.Holds]
            rw [elementTerm_eval length distinct]
            simp only [Source.Term.eval, arguments]
            exact same
          · right
            have complete := tuples_complete model
              (fun cells => (model.named names).function symbol cells !=
                model.element (tableDefault (model.size + 1) model.functions[(symbol, arity)]?)) arity []
              ((variablesFor arity).map assignment) (by simp [variablesFor_length])
              (by simp only [List.nil_append]; exact bne_iff_ne.mpr same)
            simpa using complete
      · split at built
        · cases built
          exact dense
        · cases built

theorem predicateRows_hold {layout : Layout} {symbol : String} {arity : Nat} {label : String} {rows : List Row}
    (built : predicateRows layout model names symbol arity label = .ok rows) :
    ∀ row ∈ rows, ∀ valuation, row.formula.Holds (model.named names).interpretation valuation := by
  have dense : ∀ row ∈ predicateDense model names symbol arity label, ∀ valuation,
      row.formula.Holds (model.named names).interpretation valuation := by
    intro row member valuation
    simp only [predicateDense, List.mem_singleton] at member
    subst member
    apply treeOf_conj
    intro leaf inside
    obtain ⟨cells, _, rfl⟩ := List.mem_map.mp inside
    exact predicateCell_holds length distinct symbol cells valuation
  unfold predicateRows at built
  split at built
  · cases built
    exact dense
  · split at built
    · cases built
    · dsimp only at built
      split at built
      · cases built
        intro row member valuation
        rcases List.mem_append.mp member with early | late
        · split at early
          · cases early
          · simp only [List.mem_singleton] at early
            subst early
            apply treeOf_conj
            intro leaf inside
            obtain ⟨cells, _, rfl⟩ := List.mem_map.mp inside
            exact predicateCell_holds length distinct symbol cells valuation
        · simp only [List.mem_singleton] at late
          subst late
          apply defaultFormula_holds length distinct
          intro assignment
          have arguments : ((variablesFor arity).map Source.Term.var).map
              (Source.Term.eval (model.named names).interpretation assignment) = (variablesFor arity).map assignment := by
            simp only [List.map_map, Function.comp_def, Source.Term.eval]
          by_cases same : (model.named names).predicate symbol ((variablesFor arity).map assignment) =
              (tableDefault 2 model.predicates[(symbol, arity)]? != 0)
          · left
            unfold predicateFallback
            split
            · rename_i positive
              simp only [Formula.Holds, arguments]
              show (model.named names).predicate symbol _ = true
              rw [same]
              exact positive
            · rename_i negative
              simp only [Formula.Holds, arguments]
              show ¬ (model.named names).predicate symbol _ = true
              rw [same]
              exact negative
          · right
            have complete := tuples_complete model
              (fun cells => (model.named names).predicate symbol cells !=
                (tableDefault 2 model.predicates[(symbol, arity)]? != 0)) arity []
              ((variablesFor arity).map assignment) (by simp [variablesFor_length])
              (by simp only [List.nil_append]; exact bne_iff_ne.mpr same)
            simpa using complete
      · split at built
        · cases built
          exact dense
        · cases built

/-- Every row of the document holds in the named model. -/
theorem documentRows_hold {layout : Layout} {functions predicates : List (String × Nat)} {rows : List Row}
    (built : documentRows layout model names functions predicates = .ok rows) :
    ∀ row ∈ rows, ∀ valuation, row.formula.Holds (model.named names).interpretation valuation := by
  unfold documentRows at built
  split at built
  · cases built
  · rename_i functionPart functionsBuilt
    split at built
    · cases built
    · rename_i predicatePart predicatesBuilt
      simp only [Except.ok.injEq] at built
      subst built
      intro row member valuation
      rcases List.mem_cons.mp member with domain | later
      · subst domain
        exact domainFormula_holds length distinct valuation
      · rcases List.mem_append.mp later with early | late
        · exact symbolRows_hold (fun _ _ _ _ made => functionRows_hold length distinct made) 1 functions
            functionPart functionsBuilt row early valuation
        · exact symbolRows_hold (fun _ _ _ _ made => predicateRows_hold length distinct made) 1 predicates
            predicatePart predicatesBuilt row late valuation

end Hold

/-! The checked construction. -/

/-- What the construction gives: the element names, pairwise different, one for each element and denoting it in the
    named model; the named model gives each statement the truth value the model gives it; and the rows, built for the
    described symbols, hold in the named model. -/
def DocumentFacts (layout : Layout) (model : FiniteModel) (statements : List Formula) (names : List String)
    (rows : List Row) : Prop :=
  names.length = model.size + 1 ∧ names.Nodup ∧
    (∀ element : model.Element, (model.named names).function (names.getD element.val "") [] = element) ∧
    (∀ formula ∈ statements, ∀ valuation : String → model.Element,
      formula.Holds (model.named names).interpretation valuation ↔ formula.Holds model.interpretation valuation) ∧
    documentRows layout model names (describedFunctions statements) (describedPredicates statements) = .ok rows ∧
    ∀ row ∈ rows, ∀ valuation, row.formula.Holds (model.named names).interpretation valuation

def buildDocument (layout : Layout) (model : FiniteModel) (statements : List Formula) (objects : List String) :
    Except String (List String × List Row) :=
  match freshStem objects (objects.length + 1) "e" with
  | none => .error "export-error: no fresh element stem"
  | some stem =>
    let names := elementNames model objects stem
    if names.length = model.size + 1 ∧ names.Nodup ∧ namesAgree model names (allFunctions statements) = true then
      match documentRows layout model names (describedFunctions statements) (describedPredicates statements) with
      | .ok rows => .ok (names, rows)
      | .error problem => .error problem
    else .error "export-error: element names"

theorem buildDocument_facts {layout : Layout} {model : FiniteModel} {statements : List Formula}
    {objects : List String} {names : List String} {rows : List Row}
    (built : buildDocument layout model statements objects = .ok (names, rows)) :
    DocumentFacts layout model statements names rows := by
  unfold buildDocument at built
  split at built
  · cases built
  · rename_i stem _
    dsimp only at built
    split at built
    · rename_i checks
      obtain ⟨length, distinct, agree⟩ := checks
      split at built
      · rename_i made madeRows
        simp only [Except.ok.injEq, Prod.mk.injEq] at built
        obtain ⟨rfl, rfl⟩ := built
        exact ⟨length, distinct, named_element length distinct,
          fun formula member valuation => named_holds_iff length distinct agree member valuation,
          madeRows, documentRows_hold length distinct madeRows⟩
      · cases built
    · cases built

end Fang.TptpCandidate.FullFof.Model
