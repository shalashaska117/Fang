/- Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
   The printed document determines the model. Take any interpretation in which every statement of an exported
   document holds and in which different element names denote different values, as TPTP reads distinct objects. The
   values it gives the element names are then a one-to-one image of the model's elements, and through that image it
   agrees with the accepted model on every function and predicate symbol the document describes, at every argument
   list, and on every input distinct object: `exportDocument_determines`. With `exportDocument_describes`, those
   statements are the formulas the bundle framer reads back from the printed text. -/
import ModelExport
import Std.Data.String.ToNat

namespace Fang.TptpCandidate.FullFof.Model

open NamedQuantified (update)

/-! Reading formulas back from a model of them. -/

section Inversions
variable {D : Type} (J : Source.Interpretation D) (valuation : String → D)

theorem chainOf_conj_leaves : ∀ (first : Formula) (rest : List Formula), (chainOf .conj first rest).Holds J valuation →
    first.Holds J valuation ∧ ∀ leaf ∈ rest, leaf.Holds J valuation
  | _, [], holds => ⟨holds, fun _ member => absurd member (by simp)⟩
  | first, next :: rest, holds => by
    have inner := chainOf_conj_leaves (.pair .conj first next) rest holds
    simp only [Formula.Holds, Binary.meaning] at inner
    obtain ⟨⟨here, there⟩, later⟩ := inner
    refine ⟨here, fun leaf member => ?_⟩
    rcases List.mem_cons.mp member with same | further
    · subst same
      exact there
    · exact later leaf further

theorem chainOf_disj_some : ∀ (first : Formula) (rest : List Formula), (chainOf .disj first rest).Holds J valuation →
    first.Holds J valuation ∨ ∃ leaf ∈ rest, leaf.Holds J valuation
  | _, [], holds => Or.inl holds
  | first, next :: rest, holds => by
    rcases chainOf_disj_some (.pair .disj first next) rest holds with inner | ⟨leaf, member, there⟩
    · simp only [Formula.Holds, Binary.meaning] at inner
      rcases inner with here | there
      · exact Or.inl here
      · exact Or.inr ⟨next, by simp, there⟩
    · exact Or.inr ⟨leaf, List.mem_cons_of_mem _ member, there⟩

theorem chainAll_conj_leaves (leaves : List Formula) (holds : (chainAll .conj .truth leaves).Holds J valuation) :
    ∀ leaf ∈ leaves, leaf.Holds J valuation := by
  cases leaves with
  | nil => intro _ member; cases member
  | cons first rest =>
    obtain ⟨here, there⟩ := chainOf_conj_leaves J valuation first rest holds
    intro leaf member
    rcases List.mem_cons.mp member with same | later
    · subst same
      exact here
    · exact there leaf later

theorem chainAll_disj_some (leaves : List Formula) (holds : (chainAll .disj .falsity leaves).Holds J valuation) :
    ∃ leaf ∈ leaves, leaf.Holds J valuation := by
  cases leaves with
  | nil => exact absurd holds (by simp [chainAll, Formula.Holds])
  | cons first rest =>
    rcases chainOf_disj_some J valuation first rest holds with here | ⟨leaf, member, there⟩
    · exact ⟨first, by simp, here⟩
    · exact ⟨leaf, List.mem_cons_of_mem _ member, there⟩

theorem treeWith_conj_leaves : ∀ (fuel : Nat) (leaves : List Formula),
    (treeWith .conj .truth fuel leaves).Holds J valuation → ∀ leaf ∈ leaves, leaf.Holds J valuation
  | 0, leaves, holds => chainAll_conj_leaves J valuation leaves holds
  | fuel + 1, leaves, holds => by
    unfold treeWith at holds
    split at holds
    · exact chainAll_conj_leaves J valuation leaves holds
    · simp only [Formula.Holds, Binary.meaning] at holds
      intro leaf member
      rw [← List.take_append_drop (leaves.length / 2) leaves, List.mem_append] at member
      rcases member with early | late
      · exact treeWith_conj_leaves fuel _ holds.1 leaf early
      · exact treeWith_conj_leaves fuel _ holds.2 leaf late

theorem treeWith_disj_some : ∀ (fuel : Nat) (leaves : List Formula),
    (treeWith .disj .falsity fuel leaves).Holds J valuation → ∃ leaf ∈ leaves, leaf.Holds J valuation
  | 0, leaves, holds => chainAll_disj_some J valuation leaves holds
  | fuel + 1, leaves, holds => by
    unfold treeWith at holds
    split at holds
    · exact chainAll_disj_some J valuation leaves holds
    · simp only [Formula.Holds, Binary.meaning] at holds
      rcases holds with early | late
      · obtain ⟨leaf, member, there⟩ := treeWith_disj_some fuel _ early
        exact ⟨leaf, List.mem_of_mem_take member, there⟩
      · obtain ⟨leaf, member, there⟩ := treeWith_disj_some fuel _ late
        exact ⟨leaf, List.mem_of_mem_drop member, there⟩

theorem treeOf_conj_leaves (leaves : List Formula) (holds : (treeOf .conj .truth leaves).Holds J valuation) :
    ∀ leaf ∈ leaves, leaf.Holds J valuation :=
  treeWith_conj_leaves J valuation leaves.length leaves holds

theorem treeOf_disj_some (leaves : List Formula) (holds : (treeOf .disj .falsity leaves).Holds J valuation) :
    ∃ leaf ∈ leaves, leaf.Holds J valuation :=
  treeWith_disj_some J valuation leaves.length leaves holds

end Inversions

theorem closeAll_inverse {D : Type} (J : Source.Interpretation D) (binders : List String) (body : Formula)
    (holds : ∀ valuation, (closeAll binders body).Holds J valuation) : ∀ valuation, body.Holds J valuation := by
  induction binders with
  | nil => exact holds
  | cons binder rest ih =>
    apply ih
    intro valuation
    have outer := holds valuation
    simp only [closeAll, List.foldr_cons, Formula.Holds] at outer
    have same : update valuation binder (valuation binder) = valuation := by
      funext other
      by_cases equal : other = binder
      · subst equal
        simp [update]
      · simp [update, equal]
    have inner := outer (valuation binder)
    rw [same] at inner
    exact inner

/-- The valuation that gives each binder its value in turn, and `base` elsewhere. -/
def assign {D : Type} (binders : List String) (values : List D) (base : String → D) : String → D :=
  match binders, values with
  | binder :: rest, value :: more => update (assign rest more base) binder value
  | _, _ => base

theorem assign_map {D : Type} : ∀ (binders : List String) (values : List D) (base : String → D),
    binders.Nodup → binders.length = values.length → binders.map (assign binders values base) = values
  | [], [], _, _, _ => rfl
  | binder :: rest, value :: more, base, distinct, count => by
    have fresh := (List.nodup_cons.mp distinct).1
    have inner := assign_map rest more base (List.nodup_cons.mp distinct).2 (by simpa using count)
    simp only [List.map_cons, assign]
    congr 1
    · simp [update]
    · refine (List.map_congr_left fun other member => ?_).trans inner
      have different : other ≠ binder := fun same => fresh (same ▸ member)
      simp [update, different]
  | [], _ :: _, _, _, count => by simp at count
  | _ :: _, [], _, _, count => by simp at count

theorem map_injective {α β : Type} {f : α → β} (injective : Function.Injective f) :
    ∀ {first second : List α}, first.map f = second.map f → first = second
  | [], [], _ => rfl
  | x :: xs, y :: ys, same => by
    simp only [List.map_cons, List.cons.injEq] at same
    rw [injective same.1, map_injective injective same.2]
  | [], _ :: _, same => by simp at same
  | _ :: _, [], same => by simp at same

theorem variablesFor_nodup (arity : Nat) : (variablesFor arity).Nodup := by
  unfold variablesFor
  refine List.Pairwise.map _ (fun first second different same => different ?_) List.nodup_range
  have inner := (String.append_right_inj "X").mp same
  have equal := Nat.repr_injective inner
  omega

theorem tuples_length (model : FiniteModel) (keep : List model.Element → Bool) :
    ∀ (arity : Nat) (front cells : List model.Element), cells ∈ tuples model keep arity front →
      cells.length = front.length + arity
  | 0, front, cells, member => by
    simp only [tuples] at member
    split at member
    · simp only [List.mem_singleton] at member
      subst member
      simp
    · cases member
  | arity + 1, front, cells, member => by
    simp only [tuples, List.mem_flatMap] at member
    obtain ⟨value, _, inner⟩ := member
    have counted := tuples_length model keep arity (front ++ [value]) cells inner
    simp only [List.length_append, List.length_singleton] at counted
    omega

theorem tuples_kept (model : FiniteModel) (keep : List model.Element → Bool) :
    ∀ (arity : Nat) (front cells : List model.Element), cells ∈ tuples model keep arity front → keep cells = true
  | 0, front, cells, member => by
    simp only [tuples] at member
    split at member
    · rename_i kept
      simp only [List.mem_singleton] at member
      subst member
      exact kept
    · cases member
  | arity + 1, front, cells, member => by
    simp only [tuples, List.mem_flatMap] at member
    obtain ⟨value, _, inner⟩ := member
    exact tuples_kept model keep arity (front ++ [value]) cells inner

/-! Element values and cells in another interpretation. -/

/-- The value an interpretation gives an element's name. -/
def elementOf {D : Type} (J : Source.Interpretation D) (model : FiniteModel) (names : List String)
    (element : model.Element) : D :=
  J.function (names.getD element.val "") []

/-- Different element names denote different values, as TPTP reads distinct objects. -/
def NamesApart {D : Type} (J : Source.Interpretation D) (names : List String) : Prop :=
  ∀ first ∈ names, ∀ second ∈ names, first ≠ second → J.function first [] ≠ J.function second []

section Values
variable {D : Type} (J : Source.Interpretation D) {model : FiniteModel} (names : List String)

theorem elementTerm_eval_in (element : model.Element) (valuation : String → D) :
    (elementTerm names element.val).eval J valuation = elementOf J model names element := by
  simp only [elementTerm, Source.Term.eval, List.map_nil, elementOf]

theorem argumentsOf_eval_in (cells : List model.Element) (valuation : String → D) :
    (argumentsOf names cells).map (Source.Term.eval J valuation) = cells.map (elementOf J model names) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    simp only [argumentsOf, List.map_cons] at ih ⊢
    rw [elementTerm_eval_in, ih]

theorem functionCell_in (symbol : String) (cells : List model.Element) (valuation : String → D) :
    (functionCell model names symbol cells).Holds J valuation ↔
      J.function symbol (cells.map (elementOf J model names)) =
        elementOf J model names ((model.named names).function symbol cells) := by
  simp only [functionCell, Formula.Holds]
  rw [elementTerm_eval_in]
  simp only [Source.Term.eval]
  rw [argumentsOf_eval_in]
  exact Iff.rfl

theorem predicateCell_in (symbol : String) (cells : List model.Element) (valuation : String → D) :
    (predicateCell model names symbol cells).Holds J valuation ↔
      (J.predicate symbol (cells.map (elementOf J model names)) ↔ (model.named names).predicate symbol cells = true) := by
  unfold predicateCell
  split
  · rename_i value
    simp only [Formula.Holds]
    rw [argumentsOf_eval_in]
    simp [value]
  · rename_i value
    simp only [Formula.Holds]
    rw [argumentsOf_eval_in]
    simp [value]

theorem bindings_values (valuation : String → D) : ∀ (binders : List String) (cells : List model.Element),
    binders.length = cells.length → (∀ leaf ∈ bindings names binders cells, leaf.Holds J valuation) →
      binders.map valuation = cells.map (elementOf J model names)
  | [], [], _, _ => rfl
  | binder :: rest, cell :: more, count, holds => by
    have here := holds (.equal (.var binder) (elementTerm names cell.val)) (by simp [bindings])
    simp only [Formula.Holds, Source.Term.eval] at here
    rw [elementTerm_eval_in] at here
    have later := bindings_values valuation rest more (by simpa using count)
      (fun leaf member => holds leaf (by simp only [bindings]; exact List.mem_cons_of_mem _ member))
    simp only [List.map_cons, here, later]
  | [], _ :: _, count, _ => by simp at count
  | _ :: _, [], count, _ => by simp at count

end Values

theorem elementOf_injective {D : Type} {J : Source.Interpretation D} {model : FiniteModel} {names : List String}
    (length : names.length = model.size + 1) (distinct : names.Nodup) (apart : NamesApart J names) :
    Function.Injective (elementOf J model names) := by
  intro first second same
  have inFirst : first.val < names.length := by rw [length]; exact first.isLt
  have inSecond : second.val < names.length := by rw [length]; exact second.isLt
  have getFirst : names.getD first.val "" = names[first.val] := by
    simp [List.getD_eq_getElem?_getD, inFirst]
  have getSecond : names.getD second.val "" = names[second.val] := by
    simp [List.getD_eq_getElem?_getD, inSecond]
  by_cases equal : names[first.val] = names[second.val]
  · exact Fin.ext (distinct.eq_of_getElem_eq inFirst inSecond equal)
  · exfalso
    apply apart _ (List.getElem_mem inFirst) _ (List.getElem_mem inSecond) equal
    simpa only [elementOf, getFirst, getSecond] using same

theorem domainFormula_surjective {D : Type} {J : Source.Interpretation D} {model : FiniteModel}
    {names : List String} (holds : ∀ valuation, (domainFormula model names).Holds J valuation) :
    Function.Surjective (elementOf J model names) := by
  intro value
  have row := holds (fun _ => value)
  simp only [domainFormula, Formula.Holds] at row
  obtain ⟨leaf, member, there⟩ := treeOf_disj_some J _ _ (row value)
  obtain ⟨element, _, rfl⟩ := List.mem_map.mp member
  simp only [Formula.Holds, Source.Term.eval] at there
  rw [elementTerm_eval_in] at there
  exact ⟨element, by simpa [update] using there.symm⟩

/-! Each table is read back from its rows. -/

section Tables
variable {D : Type} {J : Source.Interpretation D} {model : FiniteModel} {names : List String}

/-- Where the default statement holds, an argument list outside the exceptions satisfies the fallback. -/
theorem defaultFormula_fallback (injective : Function.Injective (elementOf J model names)) (binders : List String)
    (distinct : binders.Nodup) (fallback : Formula) (exceptions : List (List model.Element))
    (lengths : ∀ cells ∈ exceptions, cells.length = binders.length)
    (holds : ∀ valuation, (defaultFormula names binders fallback exceptions).Holds J valuation)
    (cells : List model.Element) (count : cells.length = binders.length) (outside : cells ∉ exceptions)
    (base : String → D) : fallback.Holds J (assign binders (cells.map (elementOf J model names)) base) := by
  have values := assign_map binders (cells.map (elementOf J model names)) base distinct (by simp [count])
  have body := closeAll_inverse J binders _ holds (assign binders (cells.map (elementOf J model names)) base)
  cases exceptions with
  | nil => exact body
  | cons first rest =>
    simp only [Formula.Holds, Binary.meaning] at body
    rcases body with here | there
    · exact here
    · obtain ⟨leaf, member, tuple⟩ := treeOf_disj_some J _ _ there
      obtain ⟨other, inside, rfl⟩ := List.mem_map.mp member
      have bound := bindings_values J names _ binders other (lengths other inside).symm
        (treeOf_conj_leaves J _ _ tuple)
      rw [values] at bound
      exact absurd ((map_injective injective bound) ▸ inside) outside

/-- A function table is read back from its rows. -/
theorem functionRows_determine {layout : Layout} {symbol : String} {arity : Nat} {label : String} {rows : List Row}
    (injective : Function.Injective (elementOf J model names))
    (built : functionRows layout model names symbol arity label = .ok rows)
    (holds : ∀ row ∈ rows, ∀ valuation, row.formula.Holds J valuation) (cells : List model.Element)
    (count : cells.length = arity) :
    J.function symbol (cells.map (elementOf J model names)) =
      elementOf J model names ((model.named names).function symbol cells) := by
  let base : String → D := fun _ => elementOf J model names (model.element 0)
  have fromDense : (∀ row ∈ functionDense model names symbol arity label, ∀ valuation,
      row.formula.Holds J valuation) → J.function symbol (cells.map (elementOf J model names)) =
        elementOf J model names ((model.named names).function symbol cells) := by
    intro denseHolds
    have row := denseHolds _ (List.mem_singleton_self _) base
    have member : cells ∈ tuples model (fun _ => true) arity [] := by
      simpa using tuples_complete model (fun _ => true) arity [] cells count rfl
    exact (functionCell_in J names symbol cells base).mp
      (treeOf_conj_leaves J base _ row _ (List.mem_map_of_mem member))
  unfold functionRows at built
  split at built
  · cases built
    exact fromDense holds
  · split at built
    · cases built
    · dsimp only at built
      split at built
      · cases built
        by_cases kept : ((model.named names).function symbol cells !=
            model.element (tableDefault (model.size + 1) model.functions[(symbol, arity)]?)) = true
        · have member := tuples_complete model
            (fun cells => (model.named names).function symbol cells !=
              model.element (tableDefault (model.size + 1) model.functions[(symbol, arity)]?)) arity [] cells count
            (by simpa using kept)
          simp only [List.nil_append] at member
          revert holds member
          generalize tuples model (fun cells => (model.named names).function symbol cells !=
            model.element (tableDefault (model.size + 1) model.functions[(symbol, arity)]?)) arity [] = exceptions
          intro holds member
          cases exceptions with
          | nil => cases member
          | cons first rest =>
            have row := holds _ (List.mem_append_left _ (List.mem_singleton_self _)) base
            exact (functionCell_in J names symbol cells base).mp
              (treeOf_conj_leaves J base _ row _ (List.mem_map_of_mem member))
        · have same : (model.named names).function symbol cells =
              model.element (tableDefault (model.size + 1) model.functions[(symbol, arity)]?) := by
            simpa using kept
          have outside : cells ∉ tuples model (fun cells => (model.named names).function symbol cells !=
              model.element (tableDefault (model.size + 1) model.functions[(symbol, arity)]?)) arity [] :=
            fun member => kept (tuples_kept model _ arity [] cells member)
          have lengths : ∀ other ∈ tuples model (fun cells => (model.named names).function symbol cells !=
              model.element (tableDefault (model.size + 1) model.functions[(symbol, arity)]?)) arity [],
              other.length = (variablesFor arity).length := by
            intro other member
            rw [tuples_length model _ arity [] other member, variablesFor_length]
            simp
          have defaultHolds := holds _ (List.mem_append_right _ (List.mem_singleton_self _))
          have fallback := defaultFormula_fallback injective (variablesFor arity) (variablesFor_nodup arity) _ _
            lengths defaultHolds cells (by rw [variablesFor_length]; exact count) outside base
          have values := assign_map (variablesFor arity) (cells.map (elementOf J model names)) base
            (variablesFor_nodup arity) (by simp [variablesFor_length, count])
          simp only [functionFallback, Formula.Holds, Source.Term.eval, List.map_map, Function.comp_def] at fallback
          rw [elementTerm_eval_in, values] at fallback
          rw [same]
          exact fallback
      · split at built
        · cases built
          exact fromDense holds
        · cases built

/-- A predicate table is read back from its rows. -/
theorem predicateRows_determine {layout : Layout} {symbol : String} {arity : Nat} {label : String}
    {rows : List Row} (injective : Function.Injective (elementOf J model names))
    (built : predicateRows layout model names symbol arity label = .ok rows)
    (holds : ∀ row ∈ rows, ∀ valuation, row.formula.Holds J valuation) (cells : List model.Element)
    (count : cells.length = arity) :
    J.predicate symbol (cells.map (elementOf J model names)) ↔ (model.named names).predicate symbol cells = true := by
  let base : String → D := fun _ => elementOf J model names (model.element 0)
  have fromDense : (∀ row ∈ predicateDense model names symbol arity label, ∀ valuation,
      row.formula.Holds J valuation) → (J.predicate symbol (cells.map (elementOf J model names)) ↔
        (model.named names).predicate symbol cells = true) := by
    intro denseHolds
    have row := denseHolds _ (List.mem_singleton_self _) base
    have member : cells ∈ tuples model (fun _ => true) arity [] := by
      simpa using tuples_complete model (fun _ => true) arity [] cells count rfl
    exact (predicateCell_in J names symbol cells base).mp
      (treeOf_conj_leaves J base _ row _ (List.mem_map_of_mem member))
  unfold predicateRows at built
  split at built
  · cases built
    exact fromDense holds
  · split at built
    · cases built
    · dsimp only at built
      split at built
      · cases built
        by_cases kept : ((model.named names).predicate symbol cells !=
            (tableDefault 2 model.predicates[(symbol, arity)]? != 0)) = true
        · have member := tuples_complete model
            (fun cells => (model.named names).predicate symbol cells !=
              (tableDefault 2 model.predicates[(symbol, arity)]? != 0)) arity [] cells count (by simpa using kept)
          simp only [List.nil_append] at member
          revert holds member
          generalize tuples model (fun cells => (model.named names).predicate symbol cells !=
            (tableDefault 2 model.predicates[(symbol, arity)]? != 0)) arity [] = exceptions
          intro holds member
          cases exceptions with
          | nil => cases member
          | cons first rest =>
            have row := holds _ (List.mem_append_left _ (List.mem_singleton_self _)) base
            exact (predicateCell_in J names symbol cells base).mp
              (treeOf_conj_leaves J base _ row _ (List.mem_map_of_mem member))
        · have same : (model.named names).predicate symbol cells =
              (tableDefault 2 model.predicates[(symbol, arity)]? != 0) := by
            simpa using kept
          have outside : cells ∉ tuples model (fun cells => (model.named names).predicate symbol cells !=
              (tableDefault 2 model.predicates[(symbol, arity)]? != 0)) arity [] :=
            fun member => kept (tuples_kept model _ arity [] cells member)
          have lengths : ∀ other ∈ tuples model (fun cells => (model.named names).predicate symbol cells !=
              (tableDefault 2 model.predicates[(symbol, arity)]? != 0)) arity [],
              other.length = (variablesFor arity).length := by
            intro other member
            rw [tuples_length model _ arity [] other member, variablesFor_length]
            simp
          have defaultHolds := holds _ (List.mem_append_right _ (List.mem_singleton_self _))
          have fallback := defaultFormula_fallback injective (variablesFor arity) (variablesFor_nodup arity) _ _
            lengths defaultHolds cells (by rw [variablesFor_length]; exact count) outside base
          have values := assign_map (variablesFor arity) (cells.map (elementOf J model names)) base
            (variablesFor_nodup arity) (by simp [variablesFor_length, count])
          rw [same]
          unfold predicateFallback at fallback
          split at fallback
          · rename_i positive
            simp only [Formula.Holds, Source.Term.eval, List.map_map, Function.comp_def] at fallback
            rw [values] at fallback
            simp [positive, fallback]
          · rename_i negative
            simp only [Formula.Holds, Source.Term.eval, List.map_map, Function.comp_def] at fallback
            rw [values] at fallback
            simp only [Bool.not_eq_true] at negative
            simp [negative, fallback]
      · split at built
        · cases built
          exact fromDense holds
        · cases built

end Tables

/-! The whole document. -/

theorem symbolRows_find {make : String → Nat → String → Except String (List Row)} {kind : String} :
    ∀ (position : Nat) (symbols : List (String × Nat)) (rows : List Row),
      symbolRows make kind position symbols = .ok rows → ∀ symbol ∈ symbols,
        ∃ label part, make symbol.1 symbol.2 label = .ok part ∧ ∀ row ∈ part, row ∈ rows
  | _, [], _, _, _, member => by cases member
  | position, (head, arity) :: rest, rows, built, symbol, member => by
    simp only [symbolRows] at built
    split at built
    · cases built
    · rename_i first made
      split at built
      · cases built
      · rename_i more later
        simp only [Except.ok.injEq] at built
        subst built
        rcases List.mem_cons.mp member with same | further
        · subst same
          exact ⟨_, first, made, fun row inside => List.mem_append_left _ inside⟩
        · obtain ⟨label, part, makes, within⟩ := symbolRows_find (position + 1) rest more later symbol further
          exact ⟨label, part, makes, fun row inside => List.mem_append_right _ (within row inside)⟩

/-- Any interpretation of the document's rows in which the element names stay apart is the model up to renaming
    its elements, on every symbol the rows describe. -/
theorem documentRows_determine {layout : Layout} {model : FiniteModel} {names : List String}
    {functions predicates : List (String × Nat)} {rows : List Row} {D : Type} {J : Source.Interpretation D}
    (length : names.length = model.size + 1) (distinct : names.Nodup)
    (built : documentRows layout model names functions predicates = .ok rows)
    (holds : ∀ row ∈ rows, ∀ valuation, row.formula.Holds J valuation) (apart : NamesApart J names) :
    Function.Injective (elementOf J model names) ∧ Function.Surjective (elementOf J model names) ∧
      (∀ symbol ∈ functions, ∀ cells : List model.Element, cells.length = symbol.2 →
        J.function symbol.1 (cells.map (elementOf J model names)) =
          elementOf J model names ((model.named names).function symbol.1 cells)) ∧
      (∀ symbol ∈ predicates, ∀ cells : List model.Element, cells.length = symbol.2 →
        (J.predicate symbol.1 (cells.map (elementOf J model names)) ↔
          (model.named names).predicate symbol.1 cells = true)) := by
  have injective := elementOf_injective length distinct apart
  unfold documentRows at built
  split at built
  · cases built
  · rename_i functionPart functionsBuilt
    split at built
    · cases built
    · rename_i predicatePart predicatesBuilt
      simp only [Except.ok.injEq] at built
      subst built
      refine ⟨injective, domainFormula_surjective (holds _ (List.mem_cons_self ..)), ?_, ?_⟩
      · intro symbol member cells count
        obtain ⟨label, part, made, within⟩ := symbolRows_find 1 functions functionPart functionsBuilt symbol member
        exact functionRows_determine injective made
          (fun row inside => holds row (List.mem_cons_of_mem _ (List.mem_append_left _ (within row inside))))
          cells count
      · intro symbol member cells count
        obtain ⟨label, part, made, within⟩ :=
          symbolRows_find 1 predicates predicatePart predicatesBuilt symbol member
        exact predicateRows_determine injective made
          (fun row inside => holds row (List.mem_cons_of_mem _ (List.mem_append_right _ (within row inside))))
          cells count

/-! From the export. -/

theorem buildDocument_checks {layout : Layout} {model : FiniteModel} {statements : List Formula}
    {objects : List String} {names : List String} {rows : List Row}
    (built : buildDocument layout model statements objects = .ok (names, rows)) :
    names.length = model.size + 1 ∧ names.Nodup ∧ namesAgree model names (allFunctions statements) = true ∧
      documentRows layout model names (describedFunctions statements) (describedPredicates statements) = .ok rows ∧
      ∃ stem, names = elementNames model objects stem := by
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
        exact ⟨length, distinct, agree, madeRows, stem, rfl⟩
      · cases built
    · cases built

/-- An input distinct object names the element it denotes, when the model keeps the objects apart. -/
theorem elementName_object {model : FiniteModel} {objects : List String} {stem object : String}
    (apart : separated model objects = true) (member : object ∈ objects) :
    elementName model objects stem (model.function object []).val = object := by
  unfold elementName
  cases found : objects.find? (fun other => (model.function other []).val == (model.function object []).val) with
  | none =>
    exact absurd (List.find?_eq_none.mp found object member) (by simp)
  | some other =>
    have sameValue := List.find?_some found
    have otherMember := List.mem_of_find?_eq_some found
    simp only [beq_iff_eq] at sameValue
    by_cases same : other = object
    · exact same
    · exact absurd (Fin.ext sameValue)
        ((separated_iff model objects).mp apart other otherMember object member same)

theorem elementNames_getD {model : FiniteModel} {objects : List String} {stem : String} (element : model.Element) :
    (elementNames model objects stem).getD element.val "" = elementName model objects stem element.val := by
  simp [elementNames, List.getD_eq_getElem?_getD, element.isLt]

/-- What a printed document fixes. Any interpretation in which every statement of the document holds and the element
    names stay apart is, through the values of the names, a renaming of the accepted model's elements; it agrees with
    the model on every function and predicate symbol the document describes, at every argument list, and on every
    input distinct object when the model keeps those apart. -/
theorem exportDocument_determines {limits : Limits} {layout : Layout} {model : FiniteModel}
    {statements : List Formula} {objects : List String} {comment : Option String} {text : String}
    (exported : exportDocument limits layout model statements objects comment = .ok text) :
    ∃ names rows, documentText false comment rows = .ok text ∧
      ∀ (D : Type) (J : Source.Interpretation D), (∀ row ∈ rows, ∀ valuation, row.formula.Holds J valuation) →
        NamesApart J names →
        Function.Injective (elementOf J model names) ∧ Function.Surjective (elementOf J model names) ∧
        (∀ symbol ∈ describedFunctions statements, ∀ cells : List model.Element, cells.length = symbol.2 →
          J.function symbol.1 (cells.map (elementOf J model names)) =
            elementOf J model names (model.function symbol.1 cells)) ∧
        (∀ symbol ∈ describedPredicates statements, ∀ cells : List model.Element, cells.length = symbol.2 →
          (J.predicate symbol.1 (cells.map (elementOf J model names)) ↔ model.predicate symbol.1 cells = true)) ∧
        (separated model objects = true → ∀ object ∈ objects,
          J.function object [] = elementOf J model names (model.function object [])) := by
  unfold exportDocument at exported
  split at exported
  · cases exported
  · rename_i names rows built
    obtain ⟨length, distinct, agree, made, stem, rfl⟩ := buildDocument_checks built
    split at exported
    · rename_i printed checked printedText _
      split at exported
      · split at exported
        · cases exported
        · split at exported
          · cases exported
          · split at exported
            · cases exported
              refine ⟨elementNames model objects stem, rows, printedText, fun D J holds apart => ?_⟩
              obtain ⟨injective, surjective, functionsAgree, predicatesAgree⟩ :=
                documentRows_determine length distinct made holds apart
              refine ⟨injective, surjective, ?_, ?_, ?_⟩
              · intro symbol member cells count
                rw [functionsAgree symbol member cells count]
                congr 1
                exact named_function_agree length distinct agree
                  (mem_allFunctions.mpr (mem_describedFunctions.mp member).1) cells count
              · intro symbol member cells count
                exact predicatesAgree symbol member cells count
              · intro objectsApart object member
                simp only [elementOf]
                rw [elementNames_getD, elementName_object objectsApart member]
            · cases exported
            · cases exported
      · cases exported
    · cases exported
    · cases exported

end Fang.TptpCandidate.FullFof.Model
